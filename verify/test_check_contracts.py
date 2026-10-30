"""Regression controls for quick-check verdicts, without an exhaustive graph search.

python3 -m unittest discover -s verify -p 'test_check_contracts.py'
Requires the same numpy/networkx dependencies as the quick checks; Bash tests skip
only when Bash is unavailable. All graph mutations and fake solvers stay in temp files.
"""
import contextlib
import copy
import importlib.util
import io
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
GRAPH = HERE.parent / "graph" / "r1212_1641.graph"


def load_module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_script(name, *args):
    out = io.StringIO()
    with mock.patch.object(sys, "argv", [str(HERE / name), *map(str, args)]), contextlib.redirect_stdout(out):
        try:
            runpy.run_path(str(HERE / name), run_name="__main__")
        except SystemExit as exc:
            return exc.code, out.getvalue()
    return 0, out.getvalue()


class GraphVerdictContracts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)

    def test_supplied_graph_passes_and_rebuild_is_byte_identical(self):
        code, out = run_script("check_mathon.py", GRAPH, self.work)
        self.assertEqual(code, 0, out)
        self.assertIn("RESULT: PASS", out)
        code, out = run_script("check_projection.py", GRAPH)
        self.assertEqual(code, 0, out)
        self.assertIn("CHECK: PASS", out)
        rebuilt = self.work / "rebuilt.graph"
        code, out = run_script("rebuild_from_report.py", GRAPH, rebuilt)
        self.assertEqual(code, 0, out)
        self.assertEqual(rebuilt.read_bytes(), GRAPH.read_bytes())

    def test_planted_core_k12_is_rejected_by_mathon_and_rebuild(self):
        rows = [bytearray(row) for row in GRAPH.read_bytes().splitlines()]
        for u in range(12):
            for v in range(u + 1, 12):
                rows[u][v] = rows[v][u] = ord("1")
        planted = self.work / "planted.graph"
        planted.write_bytes(b"\n".join(rows) + b"\n")
        code, out = run_script("check_mathon.py", planted, self.work)
        self.assertEqual(code, 1, out)
        self.assertIn("equals M(797): False", out)
        code, out = run_script("rebuild_from_report.py", planted, self.work / "rebuilt.graph")
        self.assertEqual(code, 1, out)
        self.assertIn("identical: False", out)

    def test_projection_negative_controls_reject_with_verdict(self):
        for edge in ("1573:1616", "1061:1626", "1597:1627"):
            with self.subTest(edge=edge):
                code, out = run_script("check_projection.py", GRAPH, edge)
                self.assertEqual(code, 1, out)
                self.assertIn("CHECK: FAIL", out)
                self.assertRegex(out, r"RESULT: [1-9][0-9]* unresolved")

    def test_malformed_input_is_rejected_before_projection(self):
        malformed = self.work / "missing_newline.graph"
        malformed.write_bytes(GRAPH.read_bytes().rstrip(b"\n"))
        for name, args in (("check_projection.py", ()), ("check_mathon.py", (self.work,)),
                           ("rebuild_from_report.py", (self.work / "rebuilt.graph",))):
            with self.subTest(script=name):
                code, _ = run_script(name, malformed, *args)
                self.assertNotEqual(code, 0)

    def test_p101_wrong_solver_verdict_fails(self):
        fake = subprocess.CompletedProcess([], 0, "omega 1 witness 0\nnodes 1\n", "")
        with mock.patch.object(subprocess, "run", return_value=fake):
            code, out = run_script("crosscheck_p101.py", HERE / "data" / "P101_H+_4flips_plus1_126.json",
                                   "fake-solver", self.work / "p101.txt")
        self.assertEqual(code, 1, out)
        self.assertIn("RESULT: FAIL", out)

    def test_rebuild_rejects_same_file_and_hardlink_without_changing_candidate(self):
        # A same-file output used to overwrite a bad candidate before comparing it.
        data = bytearray(GRAPH.read_bytes())
        data[1] = ord("0") if data[1] == ord("1") else ord("1")
        candidate = self.work / "changed.graph"
        candidate.write_bytes(data)
        for output in (candidate, self.work / "hardlink.graph"):
            with self.subTest(output=output.name):
                if output != candidate:
                    os.link(candidate, output)
                code, _ = run_script("rebuild_from_report.py", candidate, output)
                self.assertNotEqual(code, 0)
                self.assertEqual(candidate.read_bytes(), bytes(data))
                self.assertEqual(output.read_bytes(), bytes(data))


class SolverContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mc = load_module("check_maxclique")
        cls.tm = load_module("test_maxclique")
        cls.tb = load_module("test_bruteforce")

    def test_maxclique_output_and_witness(self):
        triangle = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
        self.assertEqual(self.mc.parse_result("omega 3 witness 0 1 2\nnodes 2\n", triangle), (3, True))
        self.assertEqual(self.mc.parse_result("target 4: none\nomega <= 3\nnodes 2\n", triangle, 4), (3, False))
        for output in ("", "omega 3 witness 0 1 1\nnodes 2\n", "omega 3 witness 0 1 9\nnodes 2\n",
                       "omega 3 witness 0 1\nnodes 2\n", "omega <= 3\nnodes 2\n",
                       "omega 3 witness 0 1 2\nomega 3 witness 0 1 2\nnodes 2\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                self.mc.parse_result(output, triangle)
        with self.assertRaises(ValueError):
            self.mc.parse_result("target 4: none\nomega 3 witness 0 1 2\nnodes 2\n", triangle, 4)
        with self.assertRaises(ValueError):
            self.mc.parse_result("omega 2 witness 0 1\nnodes 1\n", [[0, 0], [0, 0]])

    def test_solver_crash_and_empty_output_propagate(self):
        with mock.patch.object(self.mc.subprocess, "run", side_effect=subprocess.CalledProcessError(3, "fake")):
            with self.assertRaises(subprocess.CalledProcessError):
                self.mc.run_solver("fake", "unused", [[0]])
        with mock.patch.object(self.mc.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
            with self.assertRaises(ValueError):
                self.mc.run_solver("fake", "unused", [[0]])

    def test_wrong_exact_omega_fails_cli(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "k2.txt"
            path.write_text("2\n01\n10\n", encoding="ascii")
            with mock.patch.object(sys, "argv", ["check_maxclique.py", "fake", str(path), "2"]), \
                    mock.patch.object(self.mc, "run_solver", return_value=(1, True)), self.assertRaises(SystemExit) as caught:
                self.mc.main()
            self.assertNotEqual(caught.exception.code, 0)

    def test_maxclique_random_and_paley_mismatches_fail(self):
        for mismatch in ("random", "paley"):
            count = 0

            def fake_run(binary, tmp, adj, target=None):
                nonlocal count
                count += 1
                if target is not None:
                    return (1, True) if target == 1 else (target - 1, False)
                return (2 if (mismatch == "random" and count <= 600)
                        or (mismatch == "paley" and count > 600) else 1), True

            with self.subTest(mismatch=mismatch), mock.patch.object(sys, "argv", ["test_maxclique.py", "fake", "unused"]), \
                    mock.patch.object(self.tm, "run", side_effect=fake_run), \
                    mock.patch.object(self.tm, "nx_omega", return_value=1), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(self.tm.main(), 1)

    def test_bruteforce_coverage_timeout_and_witness_checks(self):
        rows = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
        records = [{"v": v, "c": c, "m": sum(rows[v][w] == c for w in range(v + 1, 3)),
                    "nodes": 1, "sec": 0.0, "result": "none"} for v in range(3) for c in (0, 1)]
        records[1].update(result="found", witness_ok=True, witness=[0, 1, 2])
        self.tb.validate_records(rows, 3, records)
        invalid = [[], records[:-1], records + [records[0]]]
        for change in ({"result": "timeout"}, {"m": 99}, {"witness": [0, 1, 1]},
                       {"witness_ok": False}, {"witness": [0, 1, 9]}, {"nodes": -1}):
            bad = copy.deepcopy(records)
            bad[1].update(change)
            invalid.append(bad)
        for bad in invalid:
            with self.subTest(records=bad), self.assertRaises(ValueError):
                self.tb.validate_records(rows, 3, bad)

    def test_bruteforce_zero_exit_with_empty_or_truncated_output_fails(self):
        for data in ("", '{"v":0,"c":0'):
            def fake_run(argv, **kwargs):
                Path(argv[3]).write_text(data, encoding="ascii")

            with self.subTest(data=data), tempfile.TemporaryDirectory() as tmp, \
                    mock.patch.object(self.tb.subprocess, "run", side_effect=fake_run), self.assertRaises(ValueError):
                self.tb.run("fake", Path(tmp) / "graph", [[0, 1], [1, 0]], 2)

    def test_bruteforce_random_p101_and_planted_verdicts_fail(self):
        for mismatch in ("random", "p101", "planted"):
            count = 0

            def fake_run(binary, path, rows, t, extra=()):
                nonlocal count
                count += 1
                found = ((count <= 120 and count % 2 == 0 and mismatch != "random")
                         or (count == 122 and mismatch != "p101")
                         or (count == 123 and mismatch != "planted"))
                return [{"c": 1, "result": "found" if found else "none", "witness_ok": True}]

            with self.subTest(mismatch=mismatch), tempfile.TemporaryDirectory() as tmp, \
                    mock.patch.object(sys, "argv", ["test_bruteforce.py", "fake", tmp, str(GRAPH),
                                                    str(HERE / "data" / "P101_H+_4flips_plus1_126.json")]), \
                    mock.patch.object(self.tb, "mono_omega", return_value=2), \
                    mock.patch.object(self.tb, "run", side_effect=fake_run), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(self.tb.main(), 1)


class ShellContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bash = shutil.which("bash")
        git_bash = Path("C:/Program Files/Git/bin/bash.exe")
        if cls.bash is None and git_bash.exists():
            cls.bash = str(git_bash)
        if cls.bash is None:
            raise unittest.SkipTest("Bash unavailable")

    def run_pipeline(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            verify = work / "verify"
            verify.mkdir()
            shutil.copyfile(HERE / "run_checks.sh", verify / "run_checks.sh")
            py = work / "fake-python"
            py.write_text('''#!/usr/bin/env bash
set -eu
case "$2" in
  */check_maxclique.py)
    [ "$5" = 7 ] || exit 92
    [ "$MODE" != wrong_omega ] || exit 1
    ;;
  */check_projection.py)
    if [ "$#" -gt 3 ]; then
      case "$MODE" in
        negative_pass) echo 'CHECK: PASS'; exit 0 ;;
        negative_crash) echo 'Traceback: simulated error'; exit 1 ;;
        negative_error) echo 'simulated process error'; exit 2 ;;
      esac
      echo 'RESULT: 4 unresolved'
      echo 'CHECK: FAIL'
      exit 1
    fi
    ;;
esac
exit 0
''', encoding="ascii", newline="\n")
            cc = work / "fake-cc"
            cc.write_text('''#!/usr/bin/env bash
set -eu
printf '#!/usr/bin/env bash\\nexit 0\\n' > "$3"
chmod +x "$3"
''', encoding="ascii", newline="\n")
            py.chmod(0o755)
            cc.chmod(0o755)
            env = dict(os.environ, PY=py.as_posix(), CC=cc.as_posix(), WORK=(work / "out").as_posix(), MODE=mode)
            return subprocess.run([self.bash, str(verify / "run_checks.sh")], env=env, text=True,
                                  capture_output=True, timeout=20)

    def test_expected_negative_rejections_allow_success(self):
        result = self.run_pipeline("good")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count("CHECK: FAIL"), 3)
        self.assertIn("RESULT: PASS: all quick checks", result.stdout)

    def test_unexpected_success_crash_error_or_wrong_omega_fail_pipeline(self):
        for mode in ("negative_pass", "negative_crash", "negative_error", "wrong_omega"):
            with self.subTest(mode=mode):
                result = self.run_pipeline(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("RESULT: PASS: all quick checks", result.stdout)
                stage = "### 3." if mode == "wrong_omega" else "### 5. negative control"
                self.assertIn(stage, result.stdout, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

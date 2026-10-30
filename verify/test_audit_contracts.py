"""Regression checks for audit coverage; Lake is always a shell test double."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]
LEAN = REPO / "lean"
BASH = shutil.which("bash") or next((str(p) for p in (
    Path("C:/Program Files/Git/bin/bash.exe"),
    Path("C:/Program Files/Git/usr/bin/bash.exe"),
) if p.is_file()), None)


class DefaultTargetContract(unittest.TestCase):
    def test_default_import_closure_contains_final_theorem(self):
        pending = ["RamseyIncrement"]
        seen = set()
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            source = LEAN.joinpath(*module.split(".")).with_suffix(".lean")
            if source.is_file():
                for imported in re.findall(r"^import\s+([^\n]+)", source.read_text(encoding="utf-8"), re.M):
                    pending.extend(m for m in imported.split() if m.startswith("RamseyIncrement"))
        self.assertIn("RamseyIncrement.R1212.Main", seen)
        self.assertRegex((LEAN / "lakefile.lean").read_text(encoding="utf-8"),
                         r"@\[default_target\]\s*lean_lib\s+RamseyIncrement\b")
        self.assertIn("#print axioms RamseyIncrement.R1212.r1212_lower_bound",
                      (LEAN / "AxiomAudit.lean").read_text(encoding="utf-8"))


@unittest.skipUnless(BASH, "Bash is required for the shell audit regression checks")
class UpstreamReplayContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="r1212-audit-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "audit").mkdir()
        for filename in ("leanchecker_upstream.sh", "upstream_modules.txt", "build_r1212.sh",
                         "jobs.sh", "leanchecker_r1212.sh"):
            shutil.copyfile(LEAN / "audit" / filename, self.root / "audit" / filename)
        self.modules = (self.root / "audit/upstream_modules.txt").read_text(encoding="utf-8").splitlines()
        for module in self.modules:
            path = self.root.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- audit fixture\n", encoding="utf-8")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.calls = self.root / "calls.txt"
        self.write_stub("lake", '#!/bin/sh\nprintf "%s\\n" "$*" >> "$CALLS"\n'
                        'if [ -n "$FAIL_MODULE" ] && [ "$3" = "$FAIL_MODULE" ]; then exit 9; fi\n'
                        'if [ "$*" = "$FAIL_CALL" ]; then exit 9; fi\nexit 0\n')

    def write_stub(self, name, text):
        path = self.bin / name
        path.write_bytes(text.encode("utf-8"))
        path.chmod(0o755)

    def run_audit(self, script="leanchecker_upstream.sh", args=(), **extra_env):
        test_bin = self.bin.as_posix()
        if os.name == "nt" and self.bin.drive.endswith(":"):
            test_bin = "/" + test_bin[0].lower() + test_bin[2:]
        env = dict(os.environ, PATH=str(self.bin) + os.pathsep + str(Path(BASH).parent) + os.pathsep + os.environ.get("PATH", ""),
                   CALLS=self.calls.as_posix(), FAIL_MODULE="", FAIL_CALL="", TEST_BIN=test_bin)
        env.pop("R1212_JOBS", None)
        env.update(extra_env)
        # MSYS may prepend its own tools on startup. Set the test-double PATH
        # inside Bash, so a real find/lake cannot replace a requested fixture.
        result = subprocess.run([BASH, "-c", 'export PATH="$TEST_BIN:$PATH"; source "$0" "$@"',
                                 "audit/" + script, *args], cwd=self.root,
                                env=env, text=True, encoding="utf-8", capture_output=True, timeout=30)
        calls = self.calls.read_text(encoding="utf-8").splitlines() if self.calls.exists() else []
        return result, calls

    def test_success_replays_exactly_the_expected_modules(self):
        result, calls = self.run_audit()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["env leanchecker " + m for m in self.modules])

    def test_failed_enumeration_is_not_success(self):
        self.write_stub("find", "#!/bin/sh\nexit 9\n")
        result, calls = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("enumeration failed", result.stderr)
        self.assertEqual(calls, [])

    def test_empty_enumeration_is_not_success(self):
        self.write_stub("find", "#!/bin/sh\nexit 0\n")
        result, calls = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("module set differs", result.stderr)
        self.assertEqual(calls, [])

    def test_missing_module_is_rejected_before_replay(self):
        self.root.joinpath(*self.modules[0].split(".")).with_suffix(".lean").unlink()
        result, calls = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("module set differs", result.stderr)
        self.assertEqual(calls, [])

    def test_unexpected_module_is_rejected_before_replay(self):
        (self.root / "RamseyIncrement/Unexpected.lean").write_text("", encoding="utf-8")
        result, calls = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("module set differs", result.stderr)
        self.assertEqual(calls, [])

    def test_empty_manifest_is_rejected(self):
        (self.root / "audit/upstream_modules.txt").write_text("", encoding="utf-8")
        result, calls = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("expected 43", result.stderr)
        self.assertEqual(calls, [])

    def test_checker_failure_is_not_hidden(self):
        result, calls = self.run_audit(FAIL_MODULE=self.modules[5])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 43)
        self.assertIn("FAIL  " + self.modules[5], result.stderr)

    def test_build_script_checks_default_target_after_serial_branches(self):
        result, calls = self.run_audit(script="build_r1212.sh", R1212_JOBS="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get"] +
                         [f"build RamseyIncrement.R1212.H01Branch{i}" for i in range(8)] +
                         ["build", "env lean audit/AxiomAuditR1212.lean"])

    def test_build_script_stops_after_a_failed_branch(self):
        result, calls = self.run_audit(script="build_r1212.sh", R1212_JOBS="1",
                                       FAIL_CALL="build RamseyIncrement.R1212.H01Branch3")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ["exe cache get"] +
                         [f"build RamseyIncrement.R1212.H01Branch{i}" for i in range(4)])

    @staticmethod
    def branch_batches(*sizes):
        batches, start = [], 0
        for size in sizes:
            batches.append(" ".join(f"RamseyIncrement.R1212.H01Branch{i}" for i in range(start, start + size)))
            start += size
        assert start == 8
        return batches

    def test_build_script_batches_branches(self):
        result, calls = self.run_audit(script="build_r1212.sh", R1212_JOBS="3")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get"] +
                         ["build " + b for b in self.branch_batches(3, 3, 2)] +
                         ["build", "env lean audit/AxiomAuditR1212.lean"])

    def test_build_script_option_overrides_environment(self):
        result, calls = self.run_audit(script="build_r1212.sh", args=("-j", "12"), R1212_JOBS="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls[1:3], ["build " + self.branch_batches(8)[0], "build"])

    def test_invalid_job_counts_are_rejected_before_any_build(self):
        for value in ("0", "00", "-1", "two", "1.5"):
            with self.subTest(value=value):
                self.calls.unlink(missing_ok=True)
                result, calls = self.run_audit(script="build_r1212.sh", R1212_JOBS=value)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("positive integer", result.stderr)
                self.assertEqual(calls, [])
        result, calls = self.run_audit(script="build_r1212.sh", args=("-x", "2"))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])

    def test_job_count_follows_memory_size(self):
        gib = 1048576
        cases = {8: 1, 15: 1, 16: 1, 24: 2, 32: 4, 48: 6, 64: 8, 256: 8}
        script = "; ".join(f"r1212_jobs_for_mem_kb {gb * gib}" for gb in cases)
        result = subprocess.run([BASH, "-c", f'set -euo pipefail; . audit/jobs.sh; {script}'],
                                cwd=self.root, text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), [str(n) for n in cases.values()])

    def test_detected_job_count_is_reported(self):
        result, calls = self.run_audit(script="build_r1212.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stderr, r"H01Branch module\(s\) at a time|memory size unknown")
        builds = [c for c in calls if c.startswith("build RamseyIncrement.R1212.H01Branch")]
        self.assertEqual(" ".join(builds).count("H01Branch"), 8)

    def test_r1212_replay_batches_only_the_branches(self):
        result, calls = self.run_audit(script="leanchecker_r1212.sh", R1212_JOBS="4",
                                       FAIL_MODULE="RamseyIncrement.R1212.NoSuchModule")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("ok    control: a missing module is rejected", result.stdout)
        single = ["ThirdConnector.Construction", "ThirdConnector.ColourTable", "ThirdConnector.BlueEdges",
                  "ThirdConnector.RedEdges", "ThirdConnector.Projection", "ThirdConnector.BlueU",
                  "ThirdConnector.RedU", "ThirdConnector.Theorem", "R1212.Paley", "R1212.Search",
                  "R1212.H01Data"]
        after = ["R1212.H01NoK8", "R1212.PaleyClique", "R1212.Mathon", "R1212.Main"]
        self.assertEqual(calls, ["env leanchecker RamseyIncrement." + m for m in single] +
                         ["env leanchecker " + b for b in self.branch_batches(4, 4)] +
                         ["env leanchecker RamseyIncrement." + m for m in after] +
                         ["env leanchecker RamseyIncrement.R1212.NoSuchModule"])

    def test_r1212_replay_failure_is_reported(self):
        result, calls = self.run_audit(script="leanchecker_r1212.sh", R1212_JOBS="2",
                                       FAIL_MODULE="RamseyIncrement.R1212.H01Branch2")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FAIL  RamseyIncrement.R1212.H01Branch2 RamseyIncrement.R1212.H01Branch3",
                      result.stdout)


if __name__ == "__main__":
    unittest.main()

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
        for filename in ("leanchecker_upstream.sh", "upstream_modules.txt", "build_r1212.sh"):
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

    def run_audit(self, script="leanchecker_upstream.sh", **extra_env):
        test_bin = self.bin.as_posix()
        if os.name == "nt" and self.bin.drive.endswith(":"):
            test_bin = "/" + test_bin[0].lower() + test_bin[2:]
        env = dict(os.environ, PATH=str(self.bin) + os.pathsep + str(Path(BASH).parent) + os.pathsep + os.environ.get("PATH", ""),
                   CALLS=self.calls.as_posix(), FAIL_MODULE="", FAIL_CALL="", TEST_BIN=test_bin)
        env.update(extra_env)
        # MSYS may prepend its own tools on startup. Set the test-double PATH
        # inside Bash, so a real find/lake cannot replace a requested fixture.
        result = subprocess.run([BASH, "-c", 'export PATH="$TEST_BIN:$PATH"; source "$0"',
                                 "audit/" + script], cwd=self.root,
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
        result, calls = self.run_audit(script="build_r1212.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get"] +
                         [f"build RamseyIncrement.R1212.H01Branch{i}" for i in range(8)] +
                         ["build", "env lean audit/AxiomAuditR1212.lean"])

    def test_build_script_stops_after_a_failed_branch(self):
        result, calls = self.run_audit(script="build_r1212.sh",
                                       FAIL_CALL="build RamseyIncrement.R1212.H01Branch3")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ["exe cache get"] +
                         [f"build RamseyIncrement.R1212.H01Branch{i}" for i in range(4)])


if __name__ == "__main__":
    unittest.main()

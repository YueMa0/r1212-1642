"""Generator I/O regressions; only temporary output directories are written.

Run with: python -m unittest discover -s r1212_corollary/gen -p test_gen_h01_io.py
"""
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import gen_h01


class GeneratorIOTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name)

    def originals(self):
        return {path.name: path.read_bytes() for path in self.out.iterdir()
                if path.is_file()}

    def assert_no_staging(self):
        self.assertEqual(list(self.out.glob(".gen_h01-*")), [])

    def test_unicode_utf8_and_lf_with_gbk_default(self):
        real_open = io.open
        writes = []

        def gbk_default(file, mode="r", buffering=-1, encoding=None, errors=None,
                        newline=None, closefd=True, opener=None):
            if "b" not in mode and any(flag in mode for flag in "wax"):
                # Model Windows' legacy default, even on UTF-8 test hosts.
                if encoding is None:
                    encoding = "gbk"
                writes.append((encoding, newline))
            return real_open(file, mode, buffering, encoding, errors, newline,
                             closefd, opener)

        texts = {"unicode.lean": "P₇₉₇ ≥ 1642\r\nℕ\r\n",
                 "unicode.json": '{"value": "∩"}\n'}
        with mock.patch("io.open", side_effect=gbk_default):
            gen_h01.write_outputs(self.out, texts)
        self.assertEqual(writes, [("utf-8", "\n"), ("utf-8", "\n")])
        self.assertEqual((self.out / "unicode.lean").read_bytes(),
                         "P₇₉₇ ≥ 1642\nℕ\n".encode("utf-8"))
        self.assertEqual((self.out / "unicode.json").read_bytes(),
                         texts["unicode.json"].encode("utf-8"))
        self.assert_no_staging()

    def test_encoding_failure_preserves_whole_existing_batch(self):
        for name in ("first.lean", "second.lean"):
            (self.out / name).write_bytes(("original " + name).encode("ascii"))
        before = self.originals()
        with self.assertRaises(UnicodeEncodeError):
            gen_h01.write_outputs(self.out, {
                "first.lean": "replacement ℕ\n", "second.lean": "\ud800"})
        self.assertEqual(self.originals(), before)
        self.assert_no_staging()

    def test_staging_write_failure_preserves_whole_existing_batch(self):
        for name in ("first.lean", "second.lean"):
            (self.out / name).write_bytes(b"original\n")
        before = self.originals()
        real_open = io.open

        def fail_second_stage(file, mode="r", *args, **kwargs):
            if "w" in mode and Path(file).name == "second.lean":
                raise OSError("simulated staging write failure")
            return real_open(file, mode, *args, **kwargs)

        with mock.patch("io.open", side_effect=fail_second_stage):
            with self.assertRaisesRegex(OSError, "staging write failure"):
                gen_h01.write_outputs(self.out, {
                    "first.lean": "replacement ℕ\n", "second.lean": "new\n"})
        self.assertEqual(self.originals(), before)
        self.assert_no_staging()

    def test_backup_failure_occurs_before_any_replacement(self):
        for name in ("first.lean", "second.lean"):
            (self.out / name).write_bytes(b"original\n")
        before = self.originals()
        real_copy = gen_h01.shutil.copy2

        def fail_second_backup(src, dst):
            if Path(src).name == "second.lean":
                raise OSError("simulated backup failure")
            return real_copy(src, dst)

        with mock.patch.object(gen_h01.shutil, "copy2", side_effect=fail_second_backup):
            with self.assertRaisesRegex(OSError, "backup failure"):
                gen_h01.write_outputs(self.out, {
                    "first.lean": "new\n", "second.lean": "new\n"})
        self.assertEqual(self.originals(), before)
        self.assert_no_staging()

    def test_replace_failure_restores_existing_files_and_removes_new_files(self):
        (self.out / "existing.lean").write_bytes(b"original existing\n")
        (self.out / "last.lean").write_bytes(b"original last\n")
        (self.out / "unrelated.txt").write_bytes(b"unrelated\n")
        before = self.originals()
        real_replace = gen_h01.os.replace
        calls = 0

        def fail_third_replace(src, dst):
            nonlocal calls
            calls += 1
            if calls == 3:
                raise PermissionError("simulated replace failure")
            return real_replace(src, dst)

        with mock.patch.object(gen_h01.os, "replace", side_effect=fail_third_replace):
            with self.assertRaisesRegex(PermissionError, "replace failure"):
                gen_h01.write_outputs(self.out, {
                    "existing.lean": "new ℕ\n", "created.lean": "new\n",
                    "last.lean": "new\n"})
        self.assertEqual(self.originals(), before)
        self.assert_no_staging()

    def test_failed_rollback_keeps_original_backup_for_recovery(self):
        (self.out / "first.lean").write_bytes(b"original first\n")
        (self.out / "second.lean").write_bytes(b"original second\n")
        real_replace = gen_h01.os.replace
        calls = 0

        def fail_after_first_replace(src, dst):
            nonlocal calls
            calls += 1
            if calls >= 2:
                raise PermissionError("simulated persistent replace failure")
            return real_replace(src, dst)

        with mock.patch.object(gen_h01.os, "replace", side_effect=fail_after_first_replace):
            with self.assertRaisesRegex(RuntimeError, "recovery files kept at"):
                gen_h01.write_outputs(self.out, {
                    "first.lean": "new\n", "second.lean": "new\n"})
        stages = list(self.out.glob(".gen_h01-*"))
        self.assertEqual(len(stages), 1)
        self.assertEqual((stages[0] / "original" / "first.lean").read_bytes(),
                         b"original first\n")
        self.assertEqual((self.out / "second.lean").read_bytes(), b"original second\n")

    def test_cli_regenerates_all_ten_original_files_byte_for_byte(self):
        script = Path(gen_h01.__file__).resolve()
        originals_dir = script.parents[2] / "lean" / "RamseyIncrement" / "R1212"
        names = {"H01Data.lean", "H01NoK8.lean"} | {
            f"H01Branch{k}.lean" for k in range(8)}
        originals = {name: (originals_dir / name).read_bytes() for name in names}
        # Disable Python UTF-8 mode: the generator must supply its own encoding.
        result = subprocess.run(
            [sys.executable, "-X", "utf8=0", str(script), str(self.out)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
            check=False)
        self.assertEqual(result.returncode, 0, result.stderr.decode("utf-8", errors="replace"))
        self.assertIn(b"branches 148 chunk sizes [19, 19, 19, 19, 18, 18, 18, 18]",
                      result.stdout)
        self.assertEqual(self.originals(), originals)
        self.assertEqual({name: (originals_dir / name).read_bytes() for name in names},
                         originals)
        self.assert_no_staging()


if __name__ == "__main__":
    unittest.main()

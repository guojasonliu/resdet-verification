"""Non-destructive checks for launcher refusals and shutdown behavior."""
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile
import time
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "scripts/setup-sm220u.sh"


class SetupTests(unittest.TestCase):
    def run_shell(self, code):
        return subprocess.run(
            ["bash", "-c", f"source {shlex.quote(str(SCRIPT))}\n{code}"],
            text=True, capture_output=True, timeout=10,
        )

    def test_140g_fits_256g_node(self):
        result = self.run_shell("""
            awk() { echo 268435456; }
            nproc() { echo 64; }
            HEAP=140g WORKERS=32
            check_resources
        """)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_reject_old_300g_heap(self):
        result = self.run_shell("""
            awk() { echo 268435456; }
            nproc() { echo 64; }
            HEAP=300g WORKERS=32
            check_resources
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exceeds 70%", result.stderr)

    def test_reject_excessive_workers(self):
        result = self.run_shell("""
            awk() { echo 268435456; }
            nproc() { echo 64; }
            HEAP=140g WORKERS=128
            check_resources
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exceeds available", result.stderr)

    def test_unmounted_directory_never_falls_back_to_root(self):
        result = self.run_shell("""
            mountpoint() { return 1; }
            sudo() { echo UNEXPECTED_WRITE; return 99; }
            check_storage
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("refusing root-filesystem fallback", result.stderr)
        self.assertNotIn("UNEXPECTED_WRITE", result.stdout)

    def test_root_bind_mount_is_rejected(self):
        result = self.run_shell("""
            mountpoint() { return 0; }
            findmnt() {
                case "$3" in SOURCE) echo /dev/sda3;; FSTYPE) echo ext4;; MAJ:MIN) echo 8:3;; esac
            }
            sudo() { echo UNEXPECTED_WRITE; return 99; }
            check_storage
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("backed by the root filesystem", result.stderr)
        self.assertNotIn("UNEXPECTED_WRITE", result.stdout)

    def test_existing_tlc_refuses_duplicate(self):
        result = self.run_shell("""
            pgrep() { echo '7696 java -jar tla2tools.jar Resdet'; }
            no_existing_run
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("TLC process already exists", result.stderr)

    def test_empty_process_and_screen_inventory_allowed(self):
        result = self.run_shell("""
            pgrep() { return 1; }
            screen() { return 1; }
            no_existing_run
        """)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_attached_screen_also_refuses_duplicate(self):
        result = self.run_shell("""
            pgrep() { return 1; }
            screen() { printf '  123.resdet  (Attached)\\n'; }
            no_existing_run
        """)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Screen session resdet already exists", result.stderr)

    def test_requires_sufficient_explicit_drives(self):
        result = self.run_shell("validate_disks /dev/nvme0n1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("six to eight explicit", result.stderr)

    def test_six_and_eight_drive_nodes_supported(self):
        for count in (6, 8):
            with self.subTest(count=count):
                args = " ".join(f"/dev/nvme{i}n1" for i in range(count))
                result = self.run_shell(f"validate_disk_count {args}")
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_unexpected_nine_drive_selection_refused(self):
        args = " ".join(f"/dev/nvme{i}n1" for i in range(9))
        result = self.run_shell(f"validate_disk_count {args}")
        self.assertNotEqual(result.returncode, 0)

    def test_term_stops_async_child_and_records_exit(self):
        with tempfile.TemporaryDirectory(prefix="resdet-launch-test-") as directory:
            data = Path(directory)
            run = data / "research-test"
            (run / "inputs/spec").mkdir(parents=True)
            (run / "tmp").mkdir()
            (run / "settings").write_text("140g 32\n")
            code = f"""
                source {shlex.quote(str(SCRIPT))}
                DATA={shlex.quote(str(data))}
                mountpoint() {{ return 0; }}
                flock() {{ return 0; }}
                java() {{ exec python3 -c 'import time; time.sleep(60)'; }}
                run_java {shlex.quote(str(run))}
            """
            process = subprocess.Popen(
                ["bash", "-c", code], stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            )
            child = None
            try:
                deadline = time.monotonic() + 5
                while not (run / "java.pid").exists() and time.monotonic() < deadline:
                    if process.poll() is not None:
                        stdout, stderr = process.communicate()
                        self.fail(f"Launcher exited early: {stdout}\n{stderr}")
                    time.sleep(0.05)
                self.assertTrue((run / "java.pid").exists())
                child = int((run / "java.pid").read_text())
                process.send_signal(signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 143, stdout + stderr)
                self.assertEqual((run / "exit-status").read_text().strip(), "143")
                with self.assertRaises(ProcessLookupError):
                    os.kill(child, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
                if child:
                    try:
                        os.kill(child, signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == "__main__":
    unittest.main()

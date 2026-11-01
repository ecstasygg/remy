from pathlib import Path
import statistics
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory() as directory:
        directory = Path(directory)
        runner = directory / 'measure'
        subprocess.run(['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                        ROOT / 'tests/measure.c', '-o', runner], check=True)
        print('example backend bytes stack_instructions median_frame_ns checksum')
        for source in sorted((ROOT / 'examples').glob('*.remy')):
            checksums = set()
            for backend in ('baseline', 'allocated'):
                binary = directory / backend
                args = ['baseline'] if backend == 'baseline' else []
                subprocess.run([ROOT / '.build/remy', *args, source, binary],
                               check=True, capture_output=True)
                subprocess.run([ROOT / '.build/remy', 'check', binary],
                               check=True, capture_output=True)
                listing = subprocess.run([ROOT / '.build/remy', 'disassemble', binary],
                                         check=True, capture_output=True, text=True).stdout
                traffic = sum('  push ' in row or '  pop ' in row for row in listing.splitlines())
                samples = []
                for _ in range(9):
                    result = subprocess.run([runner, binary], check=True, capture_output=True,
                                            text=True, timeout=30)
                    elapsed, checksum = map(int, result.stdout.split())
                    samples.append(elapsed)
                    checksums.add(checksum)
                print(source.stem, backend, binary.stat().st_size, traffic,
                      int(statistics.median(samples)), checksum)
            assert len(checksums) == 1, (source, checksums)


if __name__ == '__main__':
    main()

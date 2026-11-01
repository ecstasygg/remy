import argparse
import os
from pathlib import Path
import secrets
import socket
import struct
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
MAGIC = b'RMA1'


def snapshot(path):
    with path.open('rb') as stream:
        before = os.fstat(stream.fileno())
        data = stream.read(65537)
        after = path.stat()
    if (before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_ino, after.st_size, after.st_mtime_ns):
        return None
    if len(data) > 65536:
        raise ValueError('source exceeds 64 KiB')
    return data


def compile_packet(compiler, source, revision, directory):
    path, packet = directory / 'source', directory / 'packet'
    path.write_bytes(source)
    with subprocess.Popen([compiler, 'package', str(revision), path, packet],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as process:
        try:
            _, error = process.communicate(timeout=30)
        except BaseException:
            process.kill()
            process.communicate()
            raise
        if process.returncode:
            raise ValueError(error.strip())
    return packet.read_bytes()


def watch(source, endpoint, compiler, interval):
    previous = None
    packet = None
    connection = None
    flight = None
    completed = None
    sent = 0.0
    revision = secrets.randbelow((1 << 32) - 1) + 1
    replies = bytearray()
    next_connection = 0.0
    source_error = None
    with tempfile.TemporaryDirectory() as directory:
        directory = Path(directory)
        try:
            while True:
                try:
                    data = snapshot(source)
                    source_error = None
                    if data is not None and data != previous:
                        previous = data
                        candidate = revision % ((1 << 32) - 1) + 1
                        try:
                            compiled = compile_packet(compiler, data, candidate, directory)
                            packet, revision = compiled, candidate
                            print(f'revision {revision}: compiled', flush=True)
                        except (ValueError, subprocess.TimeoutExpired) as error:
                            print(error, file=sys.stderr, flush=True)
                except (OSError, ValueError) as error:
                    message = str(error)
                    if message != source_error:
                        print(message, file=sys.stderr, flush=True)
                        source_error = message
                try:
                    if connection is None:
                        if time.monotonic() < next_connection:
                            time.sleep(interval)
                            continue
                        connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                        connection.settimeout(1)
                        connection.connect(str(endpoint))
                        connection.settimeout(interval)
                        flight = None
                        completed = None
                        sent = 0.0
                        replies.clear()
                    if packet is not None and flight is None and revision != completed:
                        connection.settimeout(180)
                        connection.sendall(packet)
                        connection.settimeout(interval)
                        flight = revision
                        sent = time.monotonic()
                    if flight is not None and time.monotonic() - sent > 180:
                        raise TimeoutError('guest acknowledgement timed out')
                    try:
                        chunk = connection.recv(4096)
                        if not chunk:
                            raise ConnectionError('guest disconnected')
                        replies.extend(chunk)
                    except socket.timeout:
                        pass
                    while len(replies) >= 16:
                        if replies[:4] != MAGIC:
                            del replies[0]
                            continue
                        _, received, status, active = struct.unpack('<4sIII', replies[:16])
                        del replies[:16]
                        if received == 0 and status == 0:
                            completed = None
                            flight = None
                        elif received == flight:
                            completed = received
                            flight = None
                            print(f'revision {received}: ' + ('accepted' if status == 1 else f'rejected ({status}); active {active}'),
                                  flush=True)
                except OSError as error:
                    if connection is not None:
                        connection.close()
                    if sent:
                        print(str(error), file=sys.stderr, flush=True)
                    next_connection = time.monotonic() + (6 if sent else interval)
                    connection = None
                    sent = 0.0
                time.sleep(interval)
        finally:
            if connection is not None:
                connection.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('--socket', required=True, type=Path)
    parser.add_argument('--compiler', type=Path, default=ROOT / '.build/remy')
    parser.add_argument('--interval', type=float, default=0.25)
    args = parser.parse_args()
    if not 0.01 <= args.interval <= 10:
        parser.error('interval must be between 0.01 and 10 seconds')
    if not args.compiler.is_file() or not os.access(args.compiler, os.X_OK):
        parser.error('build an executable compiler with make first')
    try:
        watch(args.source, args.socket, args.compiler.resolve(), args.interval)
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()

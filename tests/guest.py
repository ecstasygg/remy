import json
from pathlib import Path
import re
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import time

from live import message


ROOT = Path(__file__).resolve().parents[1]
ENTRY = struct.Struct('<H38sqqQ')


def image(template, destination):
    data = bytearray(template.read_bytes())
    boots = [n for n in range(min(256, len(data) // 512))
             if data[n*512+3] == 0x88 and data[n*512+510:n*512+512] == b'\x55\xaa']
    if len(boots) != 1:
        raise ValueError('expected a TempleOS RedSea ISO')
    boot = boots[0]
    offset, sectors, root, bitmap, _ = struct.unpack_from('<5q', data, boot*512+8)
    if offset != boot or len(data) % 512:
        raise ValueError('invalid RedSea geometry')
    entries = []
    size = ENTRY.unpack_from(data, root*512)[3]
    for at in range(root*512, root*512+size, ENTRY.size):
        row = ENTRY.unpack_from(data, at)
        if row[1][0]:
            entries.append(row)

    def append(payload):
        sector = len(data) // 512
        data.extend(payload)
        data.extend(bytes((-len(data)) % 512))
        return sector

    files = {p.name: p.read_bytes() for p in (ROOT / '.build/payload').iterdir()}
    for name, payload in files.items():
        if len(name.encode('ascii')) >= 38:
            raise ValueError('RedSea filename exceeds 37 bytes')
        entries.append((0x800, name.encode('ascii'), append(payload), len(payload), 0))
    once = b'Cd("::/");;\n#include "Remy.HC"\ndirectory="::/";\nif (Verify()) Live(0);\n'
    once_sector = append(once)
    home = next(row for row in entries if row[1].split(b'\0')[0] == b'Home')
    home_start, home_size = home[2:4]
    for at in range(home_start*512, home_start*512+home_size, ENTRY.size):
        if not data[at+2]:
            data[at:at+ENTRY.size] = ENTRY.pack(0x800, b'Once.HC', once_sector, len(once), 0)
            break
    else:
        raise ValueError('template Home directory has no spare entry')
    new_root = len(data) // 512
    new_size = ((len(entries)*ENTRY.size+511) // 512)*512
    entries[0] = (entries[0][0], entries[0][1], new_root, new_size, entries[0][4])
    entries[1] = (entries[1][0], entries[1][1], new_root, 0, entries[1][4])
    append(b''.join(ENTRY.pack(*row) for row in entries))
    for row in entries[2:]:
        if row[0] & 0x10:
            parent = row[2]*512+ENTRY.size
            if ENTRY.unpack_from(data, parent)[1].split(b'\0')[0] == b'..':
                struct.pack_into('<q', data, parent+40, new_root)
    data.extend(bytes((-len(data)) % 2048))
    total = len(data) // 512
    if total - (offset + bitmap) >= bitmap*512*8:
        raise ValueError('template allocation bitmap is too small')
    struct.pack_into('<q', data, boot*512+16, total-offset)
    struct.pack_into('<q', data, boot*512+24, new_root)
    first = offset + bitmap
    for sector in range(offset+sectors, total):
        bit = sector-first
        data[(offset+1)*512+bit//8] |= 1 << (bit % 8)
    for sector in (16,18):
        struct.pack_into('<I', data, sector*2048+80, len(data)//2048)
        struct.pack_into('>I', data, sector*2048+84, len(data)//2048)
        struct.pack_into('<I', data, sector*2048+152, new_root)
        struct.pack_into('>I', data, sector*2048+156, new_root)
    destination.write_bytes(data)


def exact(connection, count):
    result = bytearray()
    while len(result) < count:
        data = connection.recv(count-len(result))
        if not data:
            raise ConnectionError('guest serial connection closed')
        result.extend(data)
    return bytes(result)


def reply(connection):
    prefix = bytearray(exact(connection, 4))
    while prefix != b'RMA1':
        prefix.pop(0)
        prefix.extend(exact(connection, 1))
    return struct.unpack('<III', exact(connection, 12))


def packet(source, revision, directory):
    text, binary = directory / 'source', directory / 'packet'
    text.write_text(source)
    subprocess.run([ROOT / '.build/remy', 'package', str(revision), text, binary],
                   check=True, capture_output=True, timeout=30)
    return binary.read_bytes()


def checksum(data):
    value = 14695981039346656037
    for byte in data:
        value = ((value ^ byte)*1099511628211) & ((1 << 64)-1)
    return value


def screen(qmp, path):
    qmp.write(json.dumps({'execute':'screendump','arguments':{'filename':str(path)}}).encode()+b'\n')
    while True:
        response = json.loads(qmp.readline())
        if 'return' in response:
            break
        if 'error' in response:
            raise RuntimeError(response)
    data = path.read_bytes()
    header = re.match(rb'P6\s+(\d+)\s+(\d+)\s+255\s', data)
    if not header:
        raise ValueError('invalid QEMU PPM screenshot')
    width, height = map(int, header.groups())
    assert width >= 560 and height >= 400
    pixels = data[header.end():]
    return b''.join(pixels[(y*width+80)*3:(y*width+560)*3] for y in range(64,400))


def main():
    if len(sys.argv) != 2 or not sys.argv[1]:
        raise SystemExit('usage: python3 tests/guest.py TempleOS.ISO')
    destination = ROOT / '.build/guest.iso'
    image(Path(sys.argv[1]), destination)
    with tempfile.TemporaryDirectory(prefix='remy') as directory:
        directory = Path(directory)
        serial, monitor = directory / 'serial', directory / 'qmp'
        log = (ROOT / '.build/guest.log').open('wb')
        process = subprocess.Popen(['qemu-system-x86_64','-m','512','-smp','2',
            '-accel','tcg,thread=multi','-cdrom',destination,'-boot','d','-display','none',
            '-monitor','none','-no-reboot','-chardev',f'socket,id=live,path={serial},server=on,wait=off',
            '-serial','chardev:live','-qmp',f'unix:{monitor},server=on,wait=off'],stdout=log,stderr=log)
        connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        qmp = None
        watcher = None
        try:
            until = time.monotonic()+15
            while not serial.exists() or not monitor.exists():
                if time.monotonic()>until or process.poll() is not None:
                    raise RuntimeError('QEMU did not start')
                time.sleep(0.1)
            connection.connect(str(serial))
            connection.settimeout(90)
            control.connect(str(monitor))
            control.settimeout(5)
            qmp = control.makefile('rwb',buffering=0)
            json.loads(qmp.readline())
            qmp.write(b'{"execute":"qmp_capabilities"}\n')
            while 'return' not in json.loads(qmp.readline()):
                pass
            assert reply(connection) == (0,0,0)
            print('guest booted and verified all three payloads',flush=True)
            connection.settimeout(30)
            connection.sendall(packet('(+ x y)',1,directory))
            assert reply(connection) == (1,1,1)
            time.sleep(1)
            before = screen(qmp,ROOT / '.build/first.ppm')
            second = packet('(if (< x y) (+ x 3) (- y 9))',2,directory)
            connection.sendall(second)
            assert reply(connection) == (2,1,2)
            time.sleep(1)
            after = screen(qmp,ROOT / '.build/second.ppm')
            assert before != after, 'accepted revision did not change rendered pixels'
            print('guest changed rendered pixels after two verified revisions',flush=True)
            corrupt = bytearray(packet('(xor x y)',3,directory))
            corrupt[-1] ^= 1
            connection.sendall(corrupt)
            assert reply(connection) == (3,2,2)
            corrupt = bytearray(packet('(xor x y)',4,directory))
            corrupt[-1] ^= 1
            struct.pack_into('<Q',corrupt,20,checksum(corrupt[:20]+corrupt[28:]))
            connection.sendall(corrupt)
            assert reply(connection) == (4,3,2)
            time.sleep(1)
            assert screen(qmp,ROOT / '.build/rejected.ppm') == after
            invalid = ((1,0),(1,65537),(1,0xffffffff),(2,0),(2,65537),(3,0),(3,513),(4,0))
            for sequence,(field,value) in enumerate(invalid,10):
                header = bytearray(packet('(xor x y)',sequence,directory)[:28])
                struct.pack_into('<I',header,4*field,value)
                connection.sendall(header)
                assert reply(connection) == (0 if field == 4 else sequence,4,2)
            print('guest rejected checksum, vector and header failures without changing the active shader',flush=True)
            connection.sendall(second[:12])
            time.sleep(6)
            connection.sendall(packet('(xor x y)',0xffffffff,directory))
            assert reply(connection) == (0xffffffff,1,0xffffffff)
            print('guest recovered from a partial frame',flush=True)
            connection.close()
            source = directory/'watch'
            source.write_text('(* x y)')
            watcher = subprocess.Popen(['python3',ROOT/'cli/watch.py',source,'--socket',serial,'--interval','0.1'],
                                       stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            message(watcher.stdout,b'accepted',timeout=90)
            time.sleep(1)
            watched = screen(qmp,ROOT / '.build/watched.ppm')
            source.write_text('(+ x)')
            message(watcher.stderr,b'syntax error',timeout=30)
            assert screen(qmp,ROOT / '.build/invalid.ppm') == watched
            source.write_text('(and x y)')
            message(watcher.stdout,b'accepted',timeout=90)
            time.sleep(1)
            final = screen(qmp,ROOT / '.build/final.ppm')
            assert final != watched
            print('watcher edits reached the real guest and an invalid source preserved its frame',flush=True)
            watcher.send_signal(signal.SIGINT)
            watcher.wait(timeout=5)
            assert watcher.returncode == 0
            qmp.write(b'{"execute":"human-monitor-command","arguments":{"command-line":"sendkey esc"}}\n')
            while 'return' not in json.loads(qmp.readline()):
                pass
            time.sleep(2)
            assert screen(qmp,ROOT / '.build/stopped.ppm') != final
            print('guest renderer and receiver stopped through Escape',flush=True)
        except Exception:
            if qmp is not None:
                try:
                    screen(qmp,ROOT / '.build/failure.ppm')
                except Exception:
                    pass
            raise
        finally:
            if watcher is not None:
                if watcher.poll() is None:
                    watcher.terminate()
                    try:
                        watcher.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        watcher.kill()
                        watcher.wait()
                watcher.stdout.close()
                watcher.stderr.close()
            connection.close()
            if qmp is not None:
                qmp.close()
            control.close()
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            log.close()


if __name__ == '__main__':
    main()

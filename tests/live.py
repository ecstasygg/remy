import os
from pathlib import Path
import select
import signal
import socket
import struct
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
HEADER = struct.Struct('<4sIIIIQ')


def checksum(data):
    value = 14695981039346656037
    for byte in data:
        value = ((value ^ byte)*1099511628211) & ((1 << 64)-1)
    return value


def exact(connection, count):
    data = bytearray()
    while len(data) < count:
        chunk = connection.recv(count-len(data))
        if not chunk:
            raise ConnectionError('watcher disconnected')
        data.extend(chunk)
    return bytes(data)


def receive(connection):
    head = exact(connection, HEADER.size)
    magic, code, source, rows, revision, digest = HEADER.unpack(head)
    assert magic == b'RMY1' and rows == 512 and 0 < revision < 1 << 32
    assert 0 < code <= 65536 and 0 < source <= 65536
    body = exact(connection, code+source+32*rows)
    assert digest == checksum(head[:20]+body)
    return head+body, body[code:code+source], revision


def acknowledge(connection, revision):
    response = struct.pack('<4sIII',b'RMA1',revision,1,revision)
    connection.sendall(response[:6])
    time.sleep(0.05)
    connection.sendall(response[6:])


def message(stream, expected, timeout=10):
    end = time.monotonic()+timeout
    data = b''
    while expected not in data:
        if not select.select([stream],[],[],max(0,end-time.monotonic()))[0]:
            raise AssertionError((expected,data))
        chunk = os.read(stream.fileno(),4096)
        if not chunk:
            raise AssertionError((expected,data))
        data += chunk


def main():
    with tempfile.TemporaryDirectory(prefix='remylive') as directory:
        directory = Path(directory)
        source, binary = directory/'source',directory/'packet'
        source.write_text('(+ x y)')
        subprocess.run([ROOT/'.build/remy','package','1',source,binary],check=True,capture_output=True)
        first = binary.read_bytes()
        magic, code, count, rows, revision, digest = HEADER.unpack(first[:28])
        assert (magic,count,rows,revision) == (b'RMY1',7,512,1)
        assert len(first) == 28+code+count+rows*32
        assert digest == checksum(first[:20]+first[28:])
        native = directory/'native'
        subprocess.run([ROOT/'.build/remy',source,native],check=True,capture_output=True)
        assert first[28:28+code] == native.read_bytes()
        vectors = first[28+code+count:]
        for at in range(0,len(vectors),32):
            x,y,t,result = struct.unpack_from('<4Q',vectors,at)
            assert result == (x+y) & ((1 << 64)-1)
        source.write_bytes(b'(+ x y);'+b'a'*(65536-8))
        subprocess.run([ROOT/'.build/remy','package',str((1 << 32)-1),source,binary],
                       check=True,capture_output=True,timeout=30)
        maximum = binary.read_bytes()
        fields = HEADER.unpack(maximum[:28])
        assert fields[2] == 65536 and fields[4] == (1 << 32)-1
        assert fields[5] == checksum(maximum[:20]+maximum[28:])
        source.write_text('(+ x y)')
        for revision in ('0',str(1 << 32),'bad'):
            binary.write_bytes(b'preserve')
            result = subprocess.run([ROOT/'.build/remy','package',revision,source,binary],capture_output=True)
            assert result.returncode and binary.read_bytes() == b'preserve'
        source.write_text('(+ x)')
        result = subprocess.run([ROOT/'.build/remy','package','2',source,binary],capture_output=True)
        assert result.returncode and binary.read_bytes() == b'preserve'
        source.write_text('(+ x y)')
        server = socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
        endpoint = directory/'serial'
        server.bind(str(endpoint))
        server.listen(1)
        server.settimeout(15)
        watcher = subprocess.Popen(['python3',ROOT/'cli/watch.py',source,'--socket',endpoint,'--interval','0.05'],
                                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        connection = None
        try:
            connection,_ = server.accept()
            connection.settimeout(10)
            original, text, revision = receive(connection)
            assert text == b'(+ x y)'
            acknowledge(connection,revision)
            message(watcher.stdout,b'accepted')
            source.write_text('(+ x)')
            message(watcher.stderr,b'syntax error')
            connection.settimeout(0.4)
            try:
                data = connection.recv(1)
            except socket.timeout:
                pass
            else:
                raise AssertionError(('invalid source produced output',data))
            connection.close()
            connection,_ = server.accept()
            connection.settimeout(10)
            resent,text,same = receive(connection)
            assert resent == original and same == revision
            acknowledge(connection,same)
            message(watcher.stdout,b'accepted')
            temporary = directory/'replacement'
            temporary.write_text('(- x y)')
            temporary.replace(source)
            updated,text,changed = receive(connection)
            assert text == b'(- x y)' and changed != revision
            message(watcher.stdout,b'compiled')
            source.write_text('(* x 3)')
            message(watcher.stdout,b'compiled')
            source.write_text('(* x 7)')
            message(watcher.stdout,b'compiled')
            connection.settimeout(0.3)
            try:
                data = connection.recv(1)
            except socket.timeout:
                pass
            else:
                raise AssertionError(('unacknowledged transfer was not coalesced',data))
            acknowledge(connection,changed)
            message(watcher.stdout,b'accepted')
            connection.settimeout(10)
            updated,text,changed = receive(connection)
            assert text == b'(* x 7)'
            acknowledge(connection,changed)
            message(watcher.stdout,b'accepted')
            connection.sendall(struct.pack('<4sIII',b'RMA1',0,0,0))
            reset,_,same = receive(connection)
            assert reset == updated and same == changed
            acknowledge(connection,same)
        finally:
            watcher.send_signal(signal.SIGINT)
            try:
                watcher.wait(timeout=5)
            except subprocess.TimeoutExpired:
                watcher.kill()
                watcher.wait()
            if connection is not None:
                connection.close()
            server.close()
            watcher.stdout.close()
            watcher.stderr.close()
        assert watcher.returncode == 0
    print('live packet bounds, independent vectors, compile rejection, fragmented replies, reconnect, atomic edits and guest restart passed')


if __name__ == '__main__':
    main()

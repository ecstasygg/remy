from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def invoke(*args, ok=True, data=None, preexec_fn=None):
    result = subprocess.run([str(ROOT / '.build/remy'), *map(str, args)], input=data,
        capture_output=True, text=True, timeout=30, preexec_fn=preexec_fn)
    assert (result.returncode == 0) == ok, (args, result.stdout, result.stderr)
    return result.stdout if ok else result.stderr


def main():
    with tempfile.TemporaryDirectory() as directory:
        source, binary = Path(directory) / 'source', Path(directory) / 'binary'
        for text, expected in [('0x0',0),('0xff',255),('0X7F',127),('0xffffffffffffffff',(1 << 64)-1),
            ('(+ 0xffffffffffffffff 1)',0),('(< 0x8000000000000000 0xffffffffffffffff)',1)]:
            source.write_text(text)
            assert int(invoke('eval',source,'0','0','0')) == expected, text
        source.write_text('(+ x y)')
        assert int(invoke('eval',source,'0xFF','0x1','0x0')) == 256
        source.write_text('(let x1 7 (let x1 (+ x1 2) (* x1 x1)))')
        assert int(invoke('eval',source,'0','0','0')) == 81
        source.write_text('(let 1x 3 1x)')
        invoke(source,binary,ok=False)
        for text in ['(+ x; ignore ) tokens\ny) ; end', '(+ x; comment\r\ny)', '(+ x y);end']:
            source.write_text(text)
            assert int(invoke('eval',source,'3','4','0')) == 7, text
        for text, position in [('(+ x)',3),('(div x y)',1),('(let a 3 b)',4),('(+ x y',4),('(+ x y) 1',5)]:
            source.write_text(text)
            assert f'token {position}\n' in invoke(source,binary,ok=False), text
        source.write_text('(+ 1 ' * 129 + '0' + ')' * 129)
        assert 'parse depth limit' in invoke(source,binary,ok=False)
        large = '0'
        for _ in range(12):
            large = f'(+ {large} {large})'
        source.write_text(large)
        assert '4096 nodes' in invoke(source,binary,ok=False)
        source.write_text('é')
        assert 'ASCII' in invoke(source,binary,ok=False)
        for text in ['0x','0x10000000000000000','0xfg','0xffextra','-0x1']:
            source.write_text(text)
            binary.write_bytes(b'preserve')
            invoke(source,binary,ok=False)
            assert binary.read_bytes() == b'preserve', text
    print('CLI literal and rejection checks passed')


if __name__ == '__main__':
    main()

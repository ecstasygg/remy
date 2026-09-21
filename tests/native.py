import ctypes
import mmap
from pathlib import Path
import platform
import random
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1
OPERATORS = ("+", "-", "*", "and", "or", "xor", "shl", "shr", "<")


def evaluate(e, env):
    if isinstance(e, int):
        return e
    if isinstance(e, str):
        return env[e]
    op, *args = e
    if op == "let":
        name, a, b = args
        return evaluate(b, {**env, name: evaluate(a, env)})
    if op == "if":
        c, a, b = args
        return evaluate(a if evaluate(c, env) else b, env)
    a, b = (evaluate(x, env) for x in args)
    return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b,
            "and": lambda: a & b, "or": lambda: a | b, "xor": lambda: a ^ b,
            "shl": lambda: a << (b & 63), "shr": lambda: a >> (b & 63),
            "<": lambda: int(a < b)}[op]() & MASK


def source(e):
    return "(" + " ".join(map(source, e)) + ")" if isinstance(e, tuple) else str(e)


def native(code):
    image = mmap.mmap(-1, len(code), prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
    image.write(code)
    address = ctypes.addressof(ctypes.c_char.from_buffer(image))
    bridge = bytes.fromhex("53 49 89 f8 49 89 f1 48 b8") + struct.pack("<Q", address) + bytes.fromhex("ff d0 5b c3")
    thunk = mmap.mmap(-1, len(bridge), prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
    thunk.write(bridge)
    function = ctypes.CFUNCTYPE(ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64)(
        ctypes.addressof(ctypes.c_char.from_buffer(thunk)))
    return function, image, thunk


def generate(rng, depth, names):
    if depth == 0 or rng.randrange(5) == 0:
        return rng.choice([0, 1, 63, 64, 65, MASK, 1 << 63, *names])
    kind = rng.randrange(5)
    if kind == 0:
        name = rng.choice(("a", "b", "c", "x"))
        return ("let", name, generate(rng, depth - 1, names), generate(rng, depth - 1, [*names, name]))
    if kind == 1:
        return ("if", *(generate(rng, depth - 1, names) for _ in range(3)))
    return (rng.choice(OPERATORS), *(generate(rng, depth - 1, names) for _ in range(2)))


def main():
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("native differential tests require an x86-64 Linux host")
    rng = random.Random(0x52454D59)
    cases = [(op, "x", "y") for op in OPERATORS]
    cases += [(op, "x", 0) for op in ("+", "-", "or", "xor", "shl", "shr")]
    cases += [("*", "x", 1), ("*", 1, "x"), ("and", "x", MASK)]
    cases += [("*", "x", 0), ("and", "x", 0), ("shl", 0, "y"), ("shr", 0, "y"), ("or", "x", MASK)]
    cases += [("if", "x", ("+", "y", "t"), ("+", "y", "t"))]
    cases += [("let", "x1", ("+", "x", 1), ("*", "x1", "x1"))]
    cases += [("let", "a", ("+", "x", 3), ("+", "y", ("let", "b", "t", ("*", "a", "b")))),
              ("let", "x", "y", ("if", "t", ("+", "x", 1), ("-", "x", 1)))]
    cases += [generate(rng, 5, ["x", "y", "t"]) for _ in range(117)]
    comparisons = 0
    with tempfile.TemporaryDirectory() as directory:
        path, binary = Path(directory) / "source", Path(directory) / "binary"
        for case in cases:
            path.write_text(source(case))
            result = subprocess.run([ROOT / ".build/remy", path, binary], capture_output=True, text=True, timeout=30)
            assert result.returncode == 0, (case, result.stderr)
            function, image, thunk = native(binary.read_bytes())
            vectors = [(a, b, a ^ b) for a in (0, 1, MASK, 1 << 63) for b in (0, 1, 63, 64, 65, MASK)]
            vectors += [tuple(rng.getrandbits(64) for _ in range(3)) for _ in range(24)]
            for x, y, t in vectors:
                expected = evaluate(case, {"x": x, "y": y, "t": t})
                actual = function(x, y, t)
                assert actual == expected, (source(case), x, y, t, expected, actual)
                comparisons += 1
            result = subprocess.run([ROOT / ".build/remy", "eval", path, str(x), str(y), str(t)],
                                    capture_output=True, text=True, timeout=30)
            assert result.returncode == 0 and int(result.stdout) == expected, (case, result.stdout, result.stderr)
            del function
            image.close()
            thunk.close()
        for bad in ("", "(+ x)", "(+ x y) 1", "(let a 3 b)", "(if 1 2)", "(let if 3 4)",
                    "18446744073709551616", "(+ x z)", "(div x y)", "é", " " * 65537):
            path.write_text(bad)
            binary.write_bytes(b"preserve")
            result = subprocess.run([ROOT / ".build/remy", path, binary], capture_output=True, timeout=30)
            assert result.returncode != 0 and binary.read_bytes() == b"preserve", bad
    print(f"{len(cases)} programs, {comparisons} native comparisons, HOL reference checks and 11 rejection cases passed")


if __name__ == "__main__":
    main()

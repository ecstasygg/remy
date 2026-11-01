Pixel expressions compile to native x86-64 for TempleOS through an Isabelle/HOL compiler, with proofs of constant folding, register allocation, bounded branching and instruction-level execution of the emitted bytes

[![i like men](media/demo.gif)](media/demo.mp4)

## Build

```sh
make check
make payload
```

It uses:
- Isabelle2026 and its bundled Poly/ML toolchain 
- Python

Copy `.build/payload/*` onto `C:/` in TempleOS and run:

```c
#include "C:/Remy.HC";
Verify;
Show(0);
```

## Usage

The byte interpreter follows encoded jumps and consumes a synthetic return address through `ret`. Compare its result with `eval` using the same `x`, `y` and `t` arguments

```sh
.build/remy examples/Rings.remy /tmp/rings.bin
.build/remy simulate /tmp/rings.bin 17 23 41
.build/remy eval examples/Rings.remy 17 23 41
```

Both evaluations return `3`. `make measure` compares the original stack backend with the current compiler on the three examples and reports bytes, static stack instructions and median host pixel-kernel time

## Live

The HOL packet builder serialises native code, its source snapshot and 512 reference rows for the trusted local compiler. The guest checks lengths, a checksum and every reference result before switching shaders between frames

`make guest` tests a copy of an official TempleOS RedSea ISO and leaves a bootable image that starts `Live(0)` automatically. Start that image with COM1 attached to a Unix socket, then edit the watched source file

```sh
make guest TEMPLE_ISO=/path/to/TempleOS.ISO
qemu-system-x86_64 -m 512 -smp 2 -cdrom .build/guest.iso \
  -chardev socket,id=live,path=/tmp/remy.sock,server=on,wait=off \
  -serial chardev:live &
python3 cli/watch.py examples/Rings.remy --socket /tmp/remy.sock
```

The watcher keeps one transfer in flight and coalesces edits while awaiting its acknowledgement. Syntax errors and rejected packets leave the current shader running, and Escape stops the guest renderer and receiver

## Correctness

Lexical bindings share the evaluation stack with spilled intermediates. The [allocator](src/Allocation.thy) keeps one intermediate in a register and adjusts variable offsets when it must spill, while the [branching compiler](src/Branches.thy) preserves the incoming frame and returns the expression result

The [encoder](src/core/Encoding.thy) proves inversion and byte bounds for immediate operands and stack displacements, while [native lowering](src/core/Native.thy) uses the following register convention to keep pixel inputs available across expression evaluation

| Registers | Role |
| --- | --- |
| `r8`, `r9`, `rdx` | Preserved inputs `x`, `y`, `t` |
| `rax` | Accumulator and result |
| `rcx`, `rbx` | Scratch |

![Source eval](media/correspondence.svg)

Arithmetic wraps modulo `2^64` and shifts mask their count to six bits

Nonconstant conditionals use forward `jz` and `jmp` instructions so only the selected arm runs. The validator checks both arms for matching stack heights and protected input registers, with a proved [512-word bound](src/Bounds.thy) above the caller frame. The HolyC runner masks each result to four bits for the TempleOS palette

The [x86 model](src/X86.thy) follows the [Intel instruction descriptions](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) for the emitted subset using a word-addressed stack. The proved function body preserves its incoming stack and pointer, then `ret` removes the return address and advances that pointer by eight bytes. Arithmetic flags that the compiler never reads are abstracted, and hardware faults, the HolyC bridge, extraction and the OS remain outside the proof

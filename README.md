# Morello Sail specification

This repository contains a Sail version of the [Morello ISA
specification][Morello], a prototype Armv8-A architecture with [CHERI][CHERI]
extensions.

The files `instrs.sail` and `v8_base.sail` in the `src` directory contain the
instruction specifications of Morello and the necessary auxiliary functions,
respectively.  These Sail files are derived from Arm's ASL specification using
the automatic [ASL-to-Sail][asl_to_sail] translation tool.  This was done using
a snapshot of ASL files provided by Arm;  compared to the version of the
specification [available on the Arm website][Morello], this snapshot consists
of plain ASL files rather than XML files, and it contains automatically
generated glue code connecting system register accessors and system operations
to the instruction semantics (e.g. `AArch64_AutoGen_SysRegRead`).

In addition, the `src` directory in this repository contains a number of Sail
files (handwritten, not derived from ASL and not part of the official
specification) that allow the generation of an executable emulator.  In
particular, `step.sail` contains a simple top-level fetch-decode-execute
function, and `impdefs.sail` and `map_clauses.sail` contain some default
choices for implementation-defined behaviour.

## Building

The release tarballs on Github contain snapshots of the artifacts generated
from the Sail specification (although for the C emulator, they contain only the
source, no binaries;  use the `gen_c` Makefile target to build a binary).

To freshly build the artifacts, make sure that a recent version of [Sail][sail]
is installed (last tested using `opam` version `sail.0.17.1`), and use the Makefile
target `gen_c` to generate an emulator, and `gen_isa` to generate a model for
the Isabelle theorem prover.

Building `morello.ir` depends additionally on `isla-sail`: 
check out a development version of `isla` (version tested `1ac01cd`), 
`cd` into `isla/isla-sail`, run `make` and then from the current path run 
`PATH=[path to isla-sail]:$PATH make gen_ir`.

The `boot.sh` script downloads, builds, and runs a (non-capability AArch64)
version of Linux above the C emulator.

Building the Rocq (Coq) definitions requires a version of Sail and [Coq-Sail]().
The script below clones and installs the latest versions of their repos.
Assuming you have opam it should work as-is. Once you've installed them in
your opam switch, run `make gen_coq` from this directory to build the Rocq
definitions or `make gen_coq_build` to additionally compile them.

```bash
# Install the latest versions of sail and coq-sail
# Tested with opam 2.2.1
opam switch create sail-cheri-riscv 4.14.1
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add coq 8.20.0
# Add sail, tested with commit 5457446
git clone https://github.com/rems-project/sail.git
cd sail
opam install .
cd ..
# Add coq-sail, tested with commit ae4cd3f
git clone https://github.com/rems-project/coq-sail.git
cd coq-sail
opam install .
```

## Usage

A formal proof of reachable capability monotonicity, the main intended security
property of the Morello architecture, using the Isabelle definitions generated
from this model is available [here][sail-morello-proofs];  see also the
[paper][morello-formal-paper] explaining the proof, as well as the automatic
generation of a test suite from earlier versions of the Sail model derived from
weekly ASL snapshots while the architecture was developed.

## License

The files in this repository are licensed under the BSD 3-Clause Clear license
in `LICENSE`.

[Morello]: https://developer.arm.com/documentation/ddi0606/latest
[CHERI]: https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/
[asl_to_sail]: https://github.com/rems-project/asl_to_sail
[sail]: https://github.com/rems-project/sail
[sail-morello-proofs]: https://github.com/CTSRD-CHERI/sail-morello-proofs
[morello-formal-paper]: https://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf

<h1 align="center">
  SYMEX
</h1>

Symex is a symbolic execution engine, producing cycle accurate Worst Case Execution Time estimates for certain architectures under certain conditions. This is achieved by operating on compile binaries for one of the following targets at the users discretion:

- ARMv6-M
- ARMv7-M/ARMv7-EM
- RISC-V (only RV32I base integer instruction set is currently supported), for the [Hippomenes architecture](https://github.com/perlindgren/hippomenes).

As the engine operates on compiled binaries it is language agnostic at the core. However, the testing has been focused on Rust applications, more specifically [`RTIC-v1`](https://github.com/rtic-rs/rtic/tree/release/v1) applications.


# Getting started

The easiest way to use Symex is by the cargo-symex tool.

Symex has support for a number of SMT solver backends, the default, and recommended, choice is [Bitwuzla](https://github.com/bitwuzla/bitwuzla).
Installing `cargo-symex` using Bitwuzla as backend, there are two options, either using a standalone, system-wide installation of Bitwuzla, or building Bitwuzla directly as part of building `symex`.

## Installing using standalone Bitwuzla

This requires Bitwuzla is installed on your system, this is typically available from your system package manager.
Once Bitwuzla has been installed, one can install `cargo-symex` by running:

```bash
cargo install --path cargo-symex
```

## Installing without standalone Bitwuzla

If installing Bitwuzla shows to be problematic, both `symex` and `cargo-symex` include a feature `build-bitwuzla` which builds `bitwuzla` instead of using the system version, this doesn't require a standalone installation of Bitwuzla, although it does require `Cadical`,  which is also typically available from your system package manager.

Once Cadical has been installed, one can install `cargo-symex` by running:

```bash
cargo install --path cargo-symex --feature=build-bitwuzla
```

<details>
  <summary>If the compiler does not find Cadical</summary>
  If you are building with bitwuzla as the solver you need to install all of bitwuzlas dependencies, this includes a SAT solver called Cadical which likely can be installed with your system package manager. Please install this and try again.
  <details>
    <summary>For Mac users</summary>
If installing Cadical via e.g. Homebrew, `rustc` does not by default look for libraries in the Homebrew lib dir, you will need to point it in the right direction.

For instance,

```
RUSTFLAGS='-L /opt/homebrew/lib' cargo install --path=cargo-symex --features=build-bitwuzla
```

adds the Homebrew lib directory to the library search path and builds and installs `cargo-symex`.
  </details>
</details>

This can then be used to compile examples or binaries and executing the (mangled) name of the function like so:

```bash
cargo symex --example [example name] --function [function name] (--release) # for examples
cargo symex --bin [example name] --function [function name] (--release) # for binaries
```

Or it can be used to run a pre-compiled binary by calling it like so
```bash
cargo symex --path [path to .elf file] --function [function name] (--release)
```


# Application notes

Analysis of compiled binaries has a few caveats, namely:

- To analyze a function it must have an entry in the `.symtab` section of the elf file. All symbols in an elf file can be shown using the `readelf -s [path to elf file]` command. To tell rustc to not mangle the function name the attribute `#[no_mangle]` can be used.
- When using symex-lib functions or to be able to detect panic the debug-data must be included in the elf file.
- Symex can be directly used as a library see `wcet-analasis-example` directory for examples of how to do that.

## Notes on the max cycle count on ARMv6-M

The max cycle count for each path is calculated by counting the number of cycles for each instruction according to [this document](https://developer.arm.com/documentation/ddi0432/c/programmers-model/instruction-set-summary). It assumes a core without wait-states.

## Notes on cycle counting for ARMv7-(E)M

The cycle counting model does not contain any model of a branch predictor. This means that the branching model always flushes the pipeline thus incurring a lot more cycles estimated as soon as a branch can be predicted by the hardware.
This could be improved greatly by adding a branch prediction model. The cycle counting model also assumes that the code encounters zero wait states, i.e. the code is running from RAM. The Cycle counts for each instruction are based on the [cortex-m4 documentation](https://developer.arm.com/documentation/ddi0439/b/CHDDIGAC).

## Note on cycle counting for RISC-V

The cycle counts are based on the single-cycle, non-pipelined [Hippomenes architecture](https://github.com/perlindgren/hippomenes).

### Limitations for ARMv7-(E)M

The ARMv7 support has partial implementations for [`DSP`](https://developer.arm.com/documentation/ddi0403/d/Application-Level-Architecture/The-ARMv7-M-Instruction-Set/Data-processing-instructions/Parallel-addition-and-subtraction-instructions--DSP-extension) and the [`floating point extension`](https://developer.arm.com/documentation/ddi0403/d/Application-Level-Architecture/Application-Level-Programmers--Model/The-optional-Floating-point-extension). The DSP extension is parsable by the [`disarmv7`](https://github.com/ivario123/disarmv7) but is not implemented in the [decoder](symex/src/general_assembly/arch/arm/v7/decoder.rs).
Armv7 has support for hardware semaphores, at the time of writing these are not implemented in Symex.
Finally, the ARMv7 ISA defines floating point operations, most of these are partially supported. However, as outlined in 2


### Future work planned or unplanned

#### Improve testing suite

The assembly to Symex GA translators needs further testing.

- The ARMv7 translator is only $\approx 26\%$ tested, due to the nature of this project we should strive to improve this.
- The ARMv6 translator lacks direct testing and should also be improved.

<details>
  <summary>Test percentage</summary>

The 26 percent comes from [llvm-test-cov](https://github.com/taiki-e/cargo-llvm-cov) which and corresponds to the lines covered. The reasoning behind including this number is simply that
it shows that more testing is needed.

</details>

#### Include [`DSP`](https://developer.arm.com/documentation/ddi0403/d/Application-Level-Architecture/The-ARMv7-M-Instruction-Set/Data-processing-instructions/Parallel-addition-and-subtraction-instructions--DSP-extension) instructions

The current (v7) implementation lacks support for [DSP](#limitations-for-armv7-em) instructions, most of these can be implemented without large changes.

#### Include support for hardware semaphores

This is nontrivial as it extensive modeling of the system if it is to be useful. However, we could implement the baseline definition from the data sheet if we simply added a hashmap to keep track of which memory addresses are subject to a semaphore.

#### Support more RISC-V instruction sets

Currently limited to RV32I base integer instruction set ([Hippomenes architecture](https://github.com/perlindgren/hippomenes)).

# Building

## Dependencies

- [bitwuzla](https://github.com/bitwuzla/bitwuzla), Bitwuzla is a Satisfiability Modulo Theories
  (SMT) solver for the theories of fixed-size bit-vectors, arrays and uninterpreted functions.
- (Optional) [boolector](https://github.com/Boolector/boolector), Boolector is a Satisfiability Modulo Theories
  (SMT) solver for the theories of fixed-size bit-vectors, arrays and uninterpreted functions.

# Debug output from SYMEX

The implementation uses the Rust log framework. You can set the logging level to the environment variable `RUST_LOG`. See below example (assumes the cargo-sub command `symex`).

```shell
> RUST_LOG=DEBUG cargo symex ...
```

If you want to narrow down the scope of logging you can give a list of modules to log.

```shell
> RUST_LOG="symex=debug" cargo symex ...
```

Symex uses different logging levels:

- info, high level logging of steps taken.
- debug, general logging of important actions.
- trace, further information on internal operations and data structures.

You can also narrow down the scope to specific modules, e.g. the executor.

```shell
> RUST_LOG="symex::executor=trace" cargo symex ...
```

# License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

# Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.


# Acknowledgement

This tool is the product three thesis projects and other course work at Luleå University Of Technology. Two of these thesis projects have been performed with financial support by [Grepit AB](https://www.grepit.se/).

The thesis projects, in chronological order, are as follows
  - [Joacim Norlén](https://github.com/norlen) [Architecture for a Symbolic Execution Environment](https://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Altu%3Adiva-92525)
  - [Erik Serrander](https://github.com/s7rul) Worst case execution time estimation using symbolic execution of
machine code (Awaiting publication)
  - [Ivar Jönsson](https://github.com/ivajon) [EASY: Static Verification and Analysis of Rust RTIC Applications](https://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Altu%3Adiva-114700)


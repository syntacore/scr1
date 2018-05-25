SCR1 is an open-source RISC-V compatible MCU core, designed by Syntacore.

## Key features
* RV32I|E[MC] ISA
* Machine privilege mode
* 2 to 4 stage pipeline
* 32-bit AXI4/AHB-Lite external interface
* Integrated IRQ controller and advanced debug
* Optimized for area and power
* Written in SystemVerilog
* Features a number of configurable parameters

For more information, see *docs/scr1_eas.pdf*.

## Repository contents
Folder | Description
------ | -----------
docs                         | SCR1 documentation
src                          | SCR1 RTL source and testbench files
tests/common                 | Common source files for tests
tests/riscv_isa              | Common source files for RISC-V ISA tests
tests/benchmarks/dhrystone21 | Dhrystone 2.1 source files
tests/vectored_isr_sample    | Simple test example for vectored interrupt mode

## Quick start guide

### Prerequisites

RISC-V GCC toolchain is required to compile the software. You can use pre-built binaries or build the toolchain from scratch.

#### Using pre-built binary tools

Pre-built RISC-V GCC toolchain and OpenOCD binaries are available to download from http://syntacore.com/page/products/sw-tools. Download the archive (*.tar.gz* for Linux, *.zip* for Windows) for your platform, extract the archive to your preferred directory and update the PATH environment variable as described in **Set environment variables** section.

#### Building tools from source

You can build the RISC-V toolchain from sources.

Build procedure is verified at the Ubuntu 14.04 LTS and Ubuntu 16.04 LTS distributions.

    sudo apt-get install autoconf automake libmpc-dev libmpfr-dev libgmp-dev gawk bison flex texinfo libtool make g++ pkg-config libexpat1-dev zlib1g-dev
    git clone https://github.com/riscv/riscv-gnu-toolchain.git
    cd riscv-gnu-toolchain
    git checkout a71fc539850f8dacf232fc580743b946c376014b
    git submodule update --init --recursive
    ./configure --prefix=<YOUR_INSTALL_PATH> --enable-multilib
    make

More detailed instructions on how to prepare and build the toolchain can be found in https://github.com/riscv/riscv-tools/blob/master/README.md.

#### Set environment variables

Add the <YOUR_INSTALL_PATH>/bin folder to the PATH environment variable:

    export PATH=$PATH:<YOUR_INSTALL_PATH>/bin

### Clone and prepare the RISC-V ISA tests

    git clone https://github.com/riscv/riscv-tests
    cd riscv-tests
    git checkout a9433c4daa287fbe101025f2a079261a10149225

Set the $RISCV_TESTS environment variable accordingly:

    export RISCV_TESTS=<PATH TO RISCV-TESTS>

### Build RTL, compile and run tests
`make run_<SIMULATOR> BUS=<AHB, AXI> RVE=<0, 1> RVM=<0, 1> IPIC=<0, 1>` will build RTL and tests, then run all tests with default parameters.

Currently supported options:
* run_modelsim
* run_vcs
* run_ncsim

Please note that RTL simulator executables should be in your PATH variable.

To run an arbitrary subset of tests, edit the *tests* target in the top Makefile, or the *rv32_tests.inc* in riscv_isa subfolder.
After all the tests have finished, the results can be found in *build/test_results.txt* (default location).

* Test build and run parameters can be configured in the *Makefile*
* SCR1 core parameters can be configured in *src/includes/scr1_arch_description.svh*

Please make sure that architectural config selected for the SCR1 RTL matches the one used for tests compilation.

## Contacts
<scr1@syntacore.com>

SCR1 is an open-source RISC-V compatible MCU core, designed and maintained by Syntacore.

## Key features
* RV32I|E[MC] ISA
* Machine privilege mode
* 2 to 4 stage pipeline
* 32-bit AXI4/AHB-Lite external interface
* Integrated IRQ controller and advanced debug
* Optimized for area and power
* Written in SystemVerilog
* Features a number of configurable parameters

For more information, see SCR1 External Architecture Specification and SCR1 User Manual.

## Repository contents
Folder | Description
------ | -----------
docs                             | SCR1 documentation
src                              | SCR1 RTL source and testbench files
sim                              | Tests and scripts for simulation
sim/tests/common                 | Common source files for tests
sim/tests/riscv_isa              | Common source files for RISC-V ISA tests
sim/tests/riscv_compliance       | Common source files for RISC-V Compliance tests
sim/tests/benchmarks/dhrystone21 | Dhrystone 2.1 source files
sim/tests/benchmarks/coremark    | Coremark platform specific source files
sim/tests/vectored_isr_sample    | Simple test example for vectored interrupt mode
sim/tests/hello                  | Simple "hello" test
sim/verilator_wrap               | Wrappers for Verilator simulation

## Quick start guide

### Prerequisites

RISC-V GCC toolchain is required to compile the software. You can use pre-built binaries or build the toolchain from scratch.

#### Using pre-built binary tools

Pre-built RISC-V GCC toolchain and OpenOCD binaries are available to download from http://syntacore.com/page/products/sw-tools. Download the archive (*.tar.gz* for Linux, *.zip* for Windows) for your platform, extract the archive to your preferred directory <GCC_INSTALL_PATH> and update the PATH environment variable as described in **Setting environment variables** section.

#### Building tools from source

You can build the RISC-V toolchain from sources.

Build procedure is verified at the Ubuntu 14.04 LTS and Ubuntu 16.04 LTS distributions.

    sudo apt-get install autoconf automake libmpc-dev libmpfr-dev libgmp-dev gawk bison flex texinfo libtool make g++ pkg-config libexpat1-dev zlib1g-dev
    git clone https://github.com/riscv/riscv-gnu-toolchain.git
    cd riscv-gnu-toolchain
    git checkout a71fc539850f8dacf232fc580743b946c376014b
    git submodule update --init --recursive
    ./configure --prefix=<GCC_INSTALL_PATH> --enable-multilib
    make

More detailed instructions on how to prepare and build the toolchain can be found in https://github.com/riscv/riscv-tools/blob/master/README.md.

#### Setting environment variables

Add the <GCC_INSTALL_PATH>/bin folder to the PATH environment variable:

    export PATH=$PATH:<GCC_INSTALL_PATH>/bin

### Included tests

By default, the simulation package includes the following tests:

* riscv_isa
* riscv_compliance
* coremark
* dhrystone21
* vectored_isr_sample
* hello

Some of the tests depend on the selected architecture (e.g. rv32i|e base, supported extensions or IPIC), and therefore can not be used for all core configurations (these are skipped automatically).

To run an arbitrary subset of tests, edit the *tests* target in the ./Makefile.
Edit the *./sim/tests/riscv_isa/rv32_tests.inc* to specify subset of RISC-V ISA tests.

#### Clone and prepare the RISC-V ISA tests

Clone RISC-V ISA tests to your preferred directory <RISCV_TESTS_PATH>

    git clone https://github.com/riscv/riscv-tests
    cd riscv-tests
    git checkout a9433c4daa287fbe101025f2a079261a10149225

Set the $RISCV_TESTS environment variable accordingly:

    export RISCV_TESTS=<RISCV_TESTS_PATH>

#### Clone RISC-V Compliance tests

Clone RISC-V Compliance tests to your preferred directory <RISCV_COMPLIANCE_TESTS_PATH>

    git clone https://github.com/riscv/riscv-compliance
    cd riscv-compliance
    git checkout 9f280717f26f50833357db9bfb77a8c79835f162

Set the $RISCV_COMPLIANCE_TESTS environment variable accordingly:

    export RISCV_COMPLIANCE_TESTS=<RISCV_COMPLIANCE_TESTS_PATH>

#### Prepare Coremark benchmark sources

Download CoreMark from EEMBC's web site and extract the archive from
http://www.eembc.org/coremark/download.php, or clone from https://github.com/eembc/coremark

Copy the following files from into the `sim/tests/benchmarks/coremark/src` directory in this repository:

* `core_main.c`
* `core_list_join.c`
* `coremark.h`
* `core_matrix.c`
* `core_state.c`
* `core_util.c`

### Running simulations 

To build RTL, compile and run tests from the repo root folder:

    make run_<SIMULATOR> BUS=<AHB, AXI> ARCH=<I, IM, IMC, IC, EM, EMC, EC> IPIC=<0, 1>

By default, the following options are used: BUS=AHB ARCH=IMC IPIC=0.

Build and run parameters can be configured in the *./Makefile*.

After all the tests have finished, the results can be found in *build/test_results.txt* (default location).

#### Simulator selection

Currently supported simulators:

* run_modelsim - Mentor Graphics ModelSim
* run_vcs - Synopsys VCS
* run_ncsim - Cadence NCSim
* run_verilator - Verilator (version >= 4.0)
* run_verilator_wf - Verilator with waveforms support

Please note that RTL simulator executables should be in your PATH variable.

For option run_verilator_wf the waveform is generated for the last executed test and is stored in ./build/simx.vcd.

#### Architectural configuration

The RISC-V toolchain automatically uses the selected ARCH for code compilation.

Please make sure that architectural configuration selected for the SCR1 RTL
matches the one used for tests compilation. SCR1 core parameters can be
configured in *./src/includes/scr1_arch_description.svh*

## SDKs

There is number of FPGA-based SCR1 SDKs available.

Please, refer to the https://github.com/syntacore/scr1-sdk for more details.

## Contacts
<scr1@syntacore.com>

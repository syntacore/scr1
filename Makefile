#------------------------------------------------------------------------------
# Makefile for SCR1
#------------------------------------------------------------------------------

# Parameters
export ARCH ?= im
export ABI  ?= ilp32
# Testbench memory delay patterns (FFFFFFFF - no delay, 00000000 - random delay, 00000001 - max delay)
imem_pattern ?= FFFFFFFF
dmem_pattern ?= FFFFFFFF

VCS_OPTS ?=
MODELSIM_OPTS ?=
NCSIM_OPTS ?=

# Paths
export root_dir := $(shell pwd)
export inc_dir := $(root_dir)/tests/common
export bld_dir := $(root_dir)/build

test_results := $(bld_dir)/test_results.txt
test_info := $(bld_dir)/test_info

# Environment
export CROSS_PREFIX ?= riscv64-unknown-elf-
export RISCV_GCC ?= $(CROSS_PREFIX)gcc
export RISCV_OBJDUMP ?= $(CROSS_PREFIX)objdump -D
export RISCV_OBJCOPY ?= $(CROSS_PREFIX)objcopy -O verilog
export RISCV_READELF ?= $(CROSS_PREFIX)readelf -s

ifeq ($(BUS),AHB)
export rtl_files  := rtl_ahb.files
export top_module := scr1_top_tb_ahb
endif

ifeq ($(BUS),AXI)
export rtl_files  := rtl_axi.files
export top_module := scr1_top_tb_axi
endif


# Targets
.PHONY: tests run_modelsim run_vcs run_ncsim

default: run_modelsim

tests: riscv_isa dhrystone21

$(test_info): clean_hex tests
	cd $(bld_dir); \
	ls -tr *.hex > $@

dhrystone21: | $(bld_dir)
	$(MAKE) -C $(root_dir)/tests/benchmarks/dhrystone21

riscv_isa: | $(bld_dir)
	$(MAKE) -C $(root_dir)/tests/riscv_isa

clean_hex: | $(bld_dir)
	$(RM) $(bld_dir)/*.hex

$(bld_dir):
	mkdir -p $(bld_dir)

run_vcs: $(test_info)
	$(MAKE) -C $(root_dir)/src build_vcs;
	printf "" > $(test_results);
	cd $(bld_dir); \
	$(bld_dir)/simv \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VCS_OPTS)

run_modelsim: $(test_info)
	$(MAKE) -C $(root_dir)/src build_modelsim; \
	printf "" > $(test_results); \
	cd $(bld_dir); \
	vsim -c -do "run -all" +nowarn3691 \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	work.$(top_module) \
	$(MODELSIM_OPTS)

run_ncsim: $(test_info)
	$(MAKE) -C $(root_dir)/src build_ncsim;
	printf "" > $(test_results);
	cd $(bld_dir); \
	irun \
	-R \
	-64bit \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(NCSIM_OPTS)

clean:
	$(MAKE) -C $(root_dir)/tests/benchmarks/dhrystone21 clean
	$(MAKE) -C $(root_dir)/tests/riscv_isa clean
	$(RM) $(test_info)

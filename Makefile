#------------------------------------------------------------------------------
# Makefile for SCR1
#------------------------------------------------------------------------------

# PARAMETERS

ARCH ?=IMC
IPIC ?=0
export BUS  ?=AHB

ARCH_lowercase = $(shell echo $(ARCH) | tr A-Z a-z)
BUS_lowercase  = $(shell echo $(BUS)  | tr A-Z a-z)
IPIC_lowercase = $(shell echo $(IPIC) | tr A-Z a-z)

ifeq ($(ARCH_lowercase),)
	export ARCH_tmp = imc
else
	ifneq (,$(findstring e,$(ARCH_lowercase)))
		ARCH_tmp   += e
		EXT_CFLAGS += -D__RVE_EXT
	else
		ARCH_tmp   += i
	endif
	ifneq (,$(findstring m,$(ARCH_lowercase)))
		ARCH_tmp   := $(ARCH_tmp)m
	endif
	ifneq (,$(findstring c,$(ARCH_lowercase)))
		ARCH_tmp   := $(ARCH_tmp)c
		EXT_CFLAGS += -D__RVC_EXT
	endif

endif

override ARCH=$(ARCH_tmp)

$(info ARCH_tmp=$(ARCH_tmp))

export TARGETS :=

export ABI   ?= ilp32
# Testbench memory delay patterns\
  (FFFFFFFF - no delay, 00000000 - random delay, 00000001 - max delay)
imem_pattern ?= FFFFFFFF
dmem_pattern ?= FFFFFFFF

VCS_OPTS       ?=
MODELSIM_OPTS  ?=
NCSIM_OPTS     ?=
VERILATOR_OPTS ?=

current_goal := $(MAKECMDGOALS:run_%=%)
ifeq ($(current_goal),)
  current_goal := verilator
endif

# Paths
export root_dir := $(shell pwd)
export tst_dir  := $(root_dir)/sim/tests
export inc_dir  := $(tst_dir)/common
export bld_dir  := $(root_dir)/build/$(current_goal)_$(BUS)_$(shell echo $(ARCH) | tr a-z A-Z)$(if $(findstring 1,$(IPIC)),_IPIC,)

test_results := $(bld_dir)/test_results.txt
test_info    := $(bld_dir)/test_info

# Environment
export CROSS_PREFIX  ?= riscv64-unknown-elf-
export RISCV_GCC     ?= $(CROSS_PREFIX)gcc
export RISCV_OBJDUMP ?= $(CROSS_PREFIX)objdump -D
export RISCV_OBJCOPY ?= $(CROSS_PREFIX)objcopy -O verilog
export RISCV_READELF ?= $(CROSS_PREFIX)readelf -s
#--
ifneq (,$(findstring axi,$(BUS_lowercase)))
export rtl_top_files := axi_top.files
export rtl_tb_files  := axi_tb.files
export top_module    := scr1_top_tb_axi
else
export rtl_top_files := ahb_top.files
export rtl_tb_files  := ahb_tb.files
export top_module    := scr1_top_tb_ahb
endif
#--
ifeq (,$(findstring e,$(ARCH_lowercase)))
ifeq (,$(findstring 0,$(IPIC)))
# comment this target if you don't want to run the vectored_isr_sample
TARGETS += vectored_isr_sample
endif

# comment this target if you don't want to run the riscv_isa
TARGETS += riscv_isa

# comment this target if you don't want to run the riscv_compliance
TARGETS += riscv_compliance
endif

# comment this target if you don't want to run the coremark
TARGETS += coremark
# comment this target if you don't want to run the dhrystone
TARGETS += dhrystone21
# comment this target if you don't want to run the hello test
TARGETS += hello

# Targets
.PHONY: tests run_modelsim run_vcs run_ncsim run_verilator run_verilator_wf

default: run_verilator

tests: $(TARGETS)

$(test_info): clean_hex tests
	cd $(bld_dir); \
	ls -tr *.hex > $@

vectored_isr_sample: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/vectored_isr_sample ARCH=$(ARCH)

dhrystone21: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/benchmarks/dhrystone21 EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

coremark: | $(bld_dir)
	-$(MAKE) -C $(tst_dir)/benchmarks/coremark EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

riscv_isa: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/riscv_isa ARCH=$(ARCH)

riscv_compliance: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/riscv_compliance ARCH=$(ARCH)

hello: | $(bld_dir)
	-$(MAKE) -C $(tst_dir)/hello EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

clean_hex: | $(bld_dir)
	$(RM) $(bld_dir)/*.hex

$(bld_dir):
	mkdir -p $(bld_dir)

run_vcs: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_vcs;
	printf "" > $(test_results);
	cd $(bld_dir); \
	$(bld_dir)/simv \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VCS_OPTS)

run_modelsim: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_modelsim; \
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
	$(MAKE) -C $(root_dir)/sim build_ncsim;
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

run_verilator: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_verilator;
	printf "" > $(test_results);
	cd $(bld_dir); \
	echo $(top_module) ; \
	$(bld_dir)/verilator/V$(top_module) \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VERILATOR_OPTS)

run_verilator_wf: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_verilator_wf;
	printf "" > $(test_results);
	cd $(bld_dir); \
	echo $(top_module) ; \
	$(bld_dir)/verilator/V$(top_module) \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VERILATOR_OPTS)

clean:
	$(MAKE) -C $(tst_dir)/benchmarks/dhrystone21 clean
	$(MAKE) -C $(tst_dir)/riscv_isa clean
	$(MAKE) -C $(tst_dir)/riscv_compliance clean
	$(RM) -R $(root_dir)/build/*
	$(RM) $(test_info)

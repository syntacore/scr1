#------------------------------------------------------------------------------
# Makefile for SCR1
#------------------------------------------------------------------------------

# PARAMETERS

# CFG = <MAX, BASE, MIN, CUSTOM>
# BUS = <AHB, AXI>

export CFG      ?= MAX
export BUS      ?= AHB

ifeq ($(CFG), MAX)
# Predefined configuration SCR1_CFG_RV32IMC_MAX
    override ARCH         := IMC
    override VECT_IRQ     := 1
    override IPIC         := 1
    override TCM          := 1
    override SIM_CFG_DEF  := SCR1_CFG_RV32IMC_MAX
else
    ifeq ($(CFG), BASE)
    # Predefined configuration SCR1_CFG_RV32IC_BASE
        override ARCH         := IC
        override VECT_IRQ     := 1
        override IPIC         := 1
        override TCM          := 1
        override SIM_CFG_DEF  := SCR1_CFG_RV32IC_BASE
    else
        ifeq ($(CFG), MIN)
        # Predefined configuration SCR1_CFG_RV32EC_MIN
            override ARCH         := EC
            override VECT_IRQ     := 0
            override IPIC         := 0
            override TCM          := 1
            override SIM_CFG_DEF  := SCR1_CFG_RV32EC_MIN
        else
        # CUSTOM configuration. Parameters can be overwritten
            # These options are for compiling tests only. Set the corresponding RTL parameters manually in the file scr1_arch_description.svh.
            # ARCH = <IMC, IC, IM, I, EMC, EM, EC, E>
            # VECT_IRQ = <0, 1>
            # IPIC = <0, 1>
            # TCM = <0, 1>
            ARCH      ?= IMC
            VECT_IRQ  ?= 0
            IPIC      ?= 0
            TCM       ?= 0
            SIM_CFG_DEF  = SCR1_CFG_$(CFG)
        endif
    endif
endif

# export all overrided variables
export ARCH
export VECT_IRQ
export IPIC
export TCM
export SIM_CFG_DEF

ARCH_lowercase = $(shell echo $(ARCH) | tr A-Z a-z)
BUS_lowercase  = $(shell echo $(BUS)  | tr A-Z a-z)

ifeq ($(ARCH_lowercase),)
    ARCH_tmp = imc
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
    ifneq (,$(findstring b,$(ARCH_lowercase)))
        ARCH_tmp   := $(ARCH_tmp)b
    endif
endif

override ARCH=$(ARCH_tmp)

# Use this parameter to enable tracelog
TRACE ?= 0

ifeq ($(TRACE), 1)
    export SIM_TRACE_DEF = SCR1_TRACE_LOG_EN
else
    export SIM_TRACE_DEF = SCR1_TRACE_LOG_DIS
endif


# Use this parameter to pass additional options for simulation build command
SIM_BUILD_OPTS ?=

# Use this parameter to set the list of tests to run
# TARGETS = <riscv_isa, riscv_compliance, riscv_arch, coremark, dhrystone21, hello, isr_sample>
export TARGETS :=


export XLEN  ?= 32
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
export bld_dir  := $(root_dir)/build/$(current_goal)_$(BUS)_$(CFG)_$(ARCH)_IPIC_$(IPIC)_TCM_$(TCM)_VIRQ_$(VECT_IRQ)_TRACE_$(TRACE)

test_results := $(bld_dir)/test_results.txt
test_info    := $(bld_dir)/test_info
sim_results  := $(bld_dir)/sim_results.txt

todo_list    := $(bld_dir)/todo.txt
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

ifneq (,$(findstring e,$(ARCH_lowercase)))
# Tests can be compiled for RVE only if gcc version 8.0.0 or higher
    GCCVERSIONGT7 := $(shell expr `$(RISCV_GCC) -dumpfullversion | cut -f1 -d'.'` \> 7)
    ifeq "$(GCCVERSIONGT7)" "1"
        ABI := ilp32e
    endif
endif

#--
ifeq (,$(findstring e,$(ARCH_lowercase)))
    # Comment this target if you don't want to run the riscv_isa
    TARGETS += riscv_isa

    # Comment this target if you don't want to run the riscv_compliance
    TARGETS += riscv_compliance

    # Comment this target if you don't want to run the riscv_arch
    TARGETS += riscv_arch
else
    # Comment this target if you don't want to run the riscv_arch
    TARGETS += riscv_arch
endif

# Comment this target if you don't want to run the isr_sample
TARGETS += isr_sample

# Comment this target if you don't want to run the coremark
TARGETS += coremark

# Comment this target if you don't want to run the dhrystone
TARGETS += dhrystone21

# Comment this target if you don't want to run the hello test
TARGETS += hello

# Comment this target if you don't want to run the watchdog test
TARGETS += watchdog

# Targets
.PHONY: tests run_modelsim run_vcs run_ncsim run_verilator run_verilator_wf

default: clean_test_list run_verilator

clean_test_list:
	rm -f $(test_info)

echo_out: tests
	@echo "                          Test               | build | simulation " ;
	@echo "$$(cat $(test_results))"

tests: $(TARGETS)

$(test_info): clean_test_list clean_hex tests
	cd $(bld_dir)

isr_sample: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/isr_sample ARCH=$(ARCH) IPIC=$(IPIC) VECT_IRQ=$(VECT_IRQ)

dhrystone21: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/benchmarks/dhrystone21 EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

coremark: | $(bld_dir)
	-$(MAKE) -C $(tst_dir)/benchmarks/coremark EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

riscv_isa: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/riscv_isa ARCH=$(ARCH)

riscv_compliance: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/riscv_compliance ARCH=$(ARCH)

riscv_arch: | $(bld_dir)
	$(MAKE) -C $(tst_dir)/riscv_arch ARCH=$(ARCH)

hello: | $(bld_dir)
	-$(MAKE) -C $(tst_dir)/hello EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

watchdog: | $(bld_dir)
	-$(MAKE) -C $(tst_dir)/watchdog EXT_CFLAGS="$(EXT_CFLAGS)" ARCH=$(ARCH)

clean_hex: | $(bld_dir)
	$(RM) $(bld_dir)/*.hex

$(bld_dir):
	mkdir -p $(bld_dir)

run_vcs: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_vcs SIM_CFG_DEF=$(SIM_CFG_DEF) SIM_TRACE_DEF=$(SIM_TRACE_DEF) SIM_BUILD_OPTS="$(SIM_BUILD_OPTS)";
	printf "" > $(test_results);
	cd $(bld_dir); \
	$(bld_dir)/simv  -V \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VCS_OPTS) | tee $(sim_results)  ;\
	printf "                          Test               | build | simulation \n" ; \
	printf "$$(cat $(test_results)) \n"
run_modelsim: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_modelsim SIM_CFG_DEF=$(SIM_CFG_DEF) SIM_TRACE_DEF=$(SIM_TRACE_DEF) SIM_BUILD_OPTS="$(SIM_BUILD_OPTS)"; \
	printf "" > $(test_results); \
	cd $(bld_dir); \
	vsim -c -do "run -all" +nowarn3691 \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	work.$(top_module) \
	$(MODELSIM_OPTS) | tee $(sim_results)  ;\
	printf "Simulation performed on $$(vsim -version) \n" ;\
	printf "                          Test               | build | simulation \n" ; \
	printf "$$(cat $(test_results)) \n"

run_ncsim: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_ncsim SIM_CFG_DEF=$(SIM_CFG_DEF) SIM_TRACE_DEF=$(SIM_TRACE_DEF) SIM_BUILD_OPTS="$(SIM_BUILD_OPTS)";
	printf "" > $(test_results);
	cd $(bld_dir); \
	irun \
	-R \
	-64bit \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(NCSIM_OPTS) | tee $(sim_results)  ;\
	printf "Simulation performed on $$(irun -version) \n" ;\
	printf "                          Test               | build | simulation \n" ; \
	printf "$$(cat $(test_results)) \n"

run_verilator: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_verilator SIM_CFG_DEF=$(SIM_CFG_DEF) SIM_TRACE_DEF=$(SIM_TRACE_DEF) SIM_BUILD_OPTS="$(SIM_BUILD_OPTS)";
	printf "" > $(test_results);
	cd $(bld_dir); \
	echo $(top_module) | tee $(sim_results); \
	$(bld_dir)/verilator/V$(top_module) \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VERILATOR_OPTS) | tee -a $(sim_results) ;\
	printf "Simulation performed on $$(verilator -version) \n" ;\
	printf "                          Test               | build | simulation \n" ; \
	printf "$$(cat $(test_results)) \n"

run_verilator_wf: $(test_info)
	$(MAKE) -C $(root_dir)/sim build_verilator_wf SIM_CFG_DEF=$(SIM_CFG_DEF) SIM_TRACE_DEF=$(SIM_TRACE_DEF) SIM_BUILD_OPTS="$(SIM_BUILD_OPTS)";
	printf "" > $(test_results);
	cd $(bld_dir); \
	echo $(top_module) | tee $(sim_results); \
	$(bld_dir)/verilator/V$(top_module) \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	$(VERILATOR_OPTS) | tee -a $(sim_results)  ;\
	printf "Simulation performed on $$(verilator -version) \n" ;\
	printf "                          Test               | build | simulation \n" ; \
	printf "$$(cat $(test_results)) \n"
clean:
	$(RM) -R $(root_dir)/build/*
#	$(MAKE) -C $(tst_dir)/benchmarks/dhrystone21 clean
#	$(MAKE) -C $(tst_dir)/riscv_isa clean
#	$(MAKE) -C $(tst_dir)/riscv_compliance clean
#	$(MAKE) -C $(tst_dir)/riscv_arch clean
#	$(RM) $(test_info)
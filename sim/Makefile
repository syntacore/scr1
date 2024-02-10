# src_dir := $(dir $(lastword $(MAKEFILE_LIST)))
rtl_src_dir := $(root_dir)/src/
rtl_core_files ?= core.files
rtl_top_files ?= ahb_top.files
rtl_tb_files ?= ahb_tb.files
rtl_inc_dir ?= $(root_dir)/src/includes
rtl_inc_tb_dir ?= $(root_dir)/src/tb
top_module ?= scr1_top_tb_ahb

rtl_core_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_core_files)))
rtl_top_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_top_files)))
rtl_tb_list := $(addprefix $(rtl_src_dir),$(shell cat $(rtl_src_dir)$(rtl_tb_files)))
sv_list := $(rtl_core_list) $(rtl_top_list) $(rtl_tb_list)

ifeq ($(MAKECMDGOALS), $(filter $(MAKECMDGOALS),build_verilator build_verilator_wf))
ifeq ($(BUS),AHB)
export scr1_wrapper  := $(root_dir)/sim/verilator_wrap/scr1_ahb_wrapper.c
endif
ifeq ($(BUS),AXI)
export scr1_wrapper  := $(root_dir)/sim/verilator_wrap/scr1_axi_wrapper.c
endif
export verilator_ver ?= $(shell  expr `verilator --version | cut -f2 -d' '`)
endif

.PHONY: build_modelsim build_vcs build_ncsim build_verilator build_verilator_wf

default: build_modelsim

build_modelsim: $(sv_list)
	cd $(bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O1 -mfcu -sv \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+nowarnSVCHK  \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_vcs: $(sv_list)
	cd $(bld_dir); \
	vcs \
	-full64 \
	-lca \
	-sverilog \
	-notice \
	+lint=all,noVCDE,noNS,noVNGS,noSVA-DIU,noSVA-CE,noSVA-NSVU \
	-timescale=1ns/1ps \
	+incdir+$(rtl_inc_dir) \
	+incdir+$(rtl_inc_tb_dir) \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	-nc \
	-debug_all \
	$(SIM_BUILD_OPTS) \
	$(sv_list)

build_ncsim: $(sv_list)
	cd $(bld_dir); \
	irun \
	-elaborate \
	-64bit \
	-disable_sem2009 \
	-verbose \
	-timescale 1ns/1ps \
	-incdir $(rtl_inc_dir) \
	-incdir $(rtl_inc_tb_dir) \
	-debug \
	+define+SCR1_TRGT_SIMULATION \
	+define+$(SIM_TRACE_DEF) \
	+define+$(SIM_CFG_DEF) \
	$(SIM_BUILD_OPTS) \
	$(sv_list) \
	-top $(top_module)

build_verilator: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	-timing \
	+1800-2017ext+sv \
	-Wno-fatal \
	--top-module $(top_module) \
	-DSCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	--clk clk \
	--exe $(scr1_wrapper) \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;

build_verilator_wf: $(sv_list)
	cd $(bld_dir); \
	verilator \
	-cc \
	-sv \
	-timing \
	+1800-2017ext+sv \
	-Wno-fatal \
	--top-module $(top_module) \
	-DSCR1_TRGT_SIMULATION \
	-D$(SIM_TRACE_DEF) \
	-D$(SIM_CFG_DEF) \
	-CFLAGS -DVCD_TRACE -CFLAGS -DTRACE_LVLV=20 \
	-CFLAGS -DVCD_FNAME=simx.vcd \
	--clk clk \
	--exe $(scr1_wrapper) \
	--trace \
	--trace-params \
    --trace-structs \
    --trace-underscore \
	--Mdir $(bld_dir)/verilator \
	-I$(rtl_inc_dir) \
	-I$(rtl_inc_tb_dir) \
	$(SIM_BUILD_OPTS) \
	$(sv_list); \
	cd verilator; \
	$(MAKE) -f V$(top_module).mk;



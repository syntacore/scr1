src_dir := $(dir $(lastword $(MAKEFILE_LIST)))
rtl_dir := $(root_dir)/src/
rtl_files ?= rtl_ahb.files
top_module ?= scr1_top_tb_ahb

rtl_list := $(addprefix $(rtl_dir),$(shell cat $(rtl_dir)$(rtl_files)))
sv_list := $(filter %.sv,$(rtl_list))

.PHONY: build_modelsim build_vcs build_ncsim

default: build_modelsim

build_modelsim: $(rtl_list)
	cd $(bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O1 -mfcu -sv +incdir+$(rtl_dir)includes +nowarnSVCHK  \
	+define+SCR1_SIM_ENV \
	$(sv_list)

build_vcs: $(rtl_list)
	cd $(bld_dir); \
	vcs \
	-full64 \
	-lca \
	-sverilog \
	-notice \
	+lint=all,noVCDE \
	-timescale=1ns/1ps \
	+incdir+$(rtl_dir)includes \
	+define+SCR1_SIM_ENV \
	-nc \
	-debug_all \
	$(sv_list)

build_ncsim: $(rtl_list)
	cd $(bld_dir); \
	irun \
	-elaborate \
	-64bit \
	-disable_sem2009 \
	-verbose \
	-timescale 1ns/1ps \
	-incdir $(rtl_dir)includes \
	-debug \
	+define+SCR1_SIM_ENV \
	$(sv_list) \
	-top $(top_module)
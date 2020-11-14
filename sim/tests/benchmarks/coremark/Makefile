src_dir := $(dir $(lastword $(MAKEFILE_LIST)))
depend_dir := $(src_dir)/../../../../dependencies/coremark

ifeq ("$(ITERATIONS)","")
ITERATIONS=1
endif

ADD_CFLAGS  += -DITERATIONS=$(ITERATIONS)
ADD_VPATH   := $(depend_dir)
ADD_incs    := -I$(src_dir)/src -I$(depend_dir)

c_src := core_portme.c sc_print.c 
coremark_src := ./src/core_list_join.c ./src/core_matrix.c ./src/core_main.c ./src/core_util.c ./src/core_state.c
c_src += core_list_join.c core_matrix.c core_main.c core_util.c core_state.c

include $(inc_dir)/common.mk

default: log_requested_tgt  $(bld_dir)/coremark.elf $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 

log_requested_tgt:
	echo coremark.hex>> $(bld_dir)/test_info

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 
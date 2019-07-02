src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

ifeq ("$(ITERATIONS)","")
ITERATIONS=1
endif

ADD_CFLAGS  += -DITERATIONS=$(ITERATIONS)
ADD_VPATH   := $(src_dir)/src
ADD_incs    := -I$(src_dir)/src

c_src := core_portme.c sc_print.c 
coremark_src := ./src/core_list_join.c ./src/core_matrix.c ./src/core_main.c ./src/core_util.c ./src/core_state.c
c_src += core_list_join.c core_matrix.c core_main.c core_util.c core_state.c

include $(inc_dir)/common.mk

default: check_coremark_src $(bld_dir)/coremark.elf $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 

check_coremark_src:
	@for i in $(coremark_src) ; do \
		if [ ! -f $$i ] ; then \
		    printf "\n\n===========================================================================================\n"; \
		    printf "Source file: $$i not exist!\n"; \
		    printf "Please download CoreMark sources and place it '/coremark/src' directory in this repository\n"; \
		    printf "===========================================================================================\n\n"; \
		    exit 1; \
		fi \
	done

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 
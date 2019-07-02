src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

c_src := sc_print.c hello.c

include $(inc_dir)/common.mk

default: $(bld_dir)/hello.elf $(bld_dir)/hello.hex $(bld_dir)/hello.dump

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/hello.elf $(bld_dir)/hello.hex $(bld_dir)/hello.dump
src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

c_src := sc_print.c hello.c

include $(inc_dir)/common.mk

default: log_requested_tgt $(bld_dir)/hello.elf $(bld_dir)/hello.hex $(bld_dir)/hello.dump

log_requested_tgt:
	echo hello.hex>> $(bld_dir)/test_info

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/hello.elf $(bld_dir)/hello.hex $(bld_dir)/hello.dump
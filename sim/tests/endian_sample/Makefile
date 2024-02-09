src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

c_src := sc_print.c endian_sample.c

include $(inc_dir)/common.mk

default: log_requested_tgt $(bld_dir)/endian_sample.elf $(bld_dir)/endian_sample.hex $(bld_dir)/endian_sample.dump

log_requested_tgt:
	echo endian_sample.hex>> $(bld_dir)/test_info

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/endian_sample.elf $(bld_dir)/endian_sample.hex $(bld_dir)/endian_sample.dump

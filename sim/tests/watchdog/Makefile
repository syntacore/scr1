src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

c_src := sc_print.c watchdog.c

include $(inc_dir)/common.mk

default: log_requested_tgt $(bld_dir)/watchdog.elf $(bld_dir)/watchdog.hex $(bld_dir)/watchdog.dump

log_requested_tgt:
	echo watchdog.hex>> $(bld_dir)/test_info

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/watchdog.elf $(bld_dir)/watchdog.hex $(bld_dir)/watchdog.dump
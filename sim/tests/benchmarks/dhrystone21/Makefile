src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

ADD_FLAGS   := -flto
ADD_CFLAGS  := -DSELF_TIMED=1 -DTIME=1

c_src := sc_print.c dhry_1.c dhry_2.c

include $(inc_dir)/common.mk

default: $(bld_dir)/dhrystone21.elf $(bld_dir)/dhrystone21.hex $(bld_dir)/dhrystone21.dump

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/dhrystone21.elf $(bld_dir)/dhrystone21.hex $(bld_dir)/dhrystone21.dump
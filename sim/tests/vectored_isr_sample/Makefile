src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

LDFLAGS := -nostartfiles -nostdlib -march=rv32$(ARCH) -mabi=$(ABI)
ADD_ASM_MACRO := -DASM

asm_src := v_isr_sample.S

include $(inc_dir)/common.mk

default: $(bld_dir)/v_isr_sample.elf $(bld_dir)/v_isr_sample.hex $(bld_dir)/v_isr_sample.dump

clean:
	$(RM)$(asm_objs) $(bld_dir)/v_isr_sample.elf $(bld_dir)/v_isr_sample.hex $(bld_dir)/v_isr_sample.dump
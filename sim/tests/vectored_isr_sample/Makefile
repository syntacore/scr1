src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

CFLAGS += $(FLAGS) \
-static -std=gnu99 -fno-common -fno-builtin-printf \
-Wa,-march=rv32$(ARCH) -march=rv32$(ARCH) -mabi=$(ABI)
LDFLAGS += -nostartfiles -nostdlib -march=rv32$(ARCH) -mabi=$(ABI)

VPATH += $(src_dir) $(inc_dir)
incs += -I$(src_dir) -I$(inc_dir)

asm_src := v_isr_sample.S

ifdef TCM
ld_script := $(inc_dir)/link_tcm.ld
else
ld_script := $(inc_dir)/link.ld
endif



asm_objs := $(addprefix $(bld_dir)/,$(patsubst %.S, %.o, $(asm_src)))

default: $(bld_dir)/v_isr_sample.elf $(bld_dir)/v_isr_sample.hex $(bld_dir)/v_isr_sample.dump

$(bld_dir)/%.o: %.S
	$(RISCV_GCC) $(CFLAGS) -DASM -c $(incs) $< -o $@

$(bld_dir)/v_isr_sample.elf: $(ld_script) $(asm_objs)
	$(RISCV_GCC) -o $@ -T $^ $(LDFLAGS)

$(bld_dir)/v_isr_sample.hex: $(bld_dir)/v_isr_sample.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/v_isr_sample.dump: $(bld_dir)/v_isr_sample.elf
	$(RISCV_OBJDUMP) $^ > $@

clean:
	$(RM)$(asm_objs) $(bld_dir)/v_isr_sample.elf $(bld_dir)/v_isr_sample.hex $(bld_dir)/v_isr_sample.dump
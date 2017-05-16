src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

test_list := $(shell cat $(src_dir)list.txt)
test_elf := $(addprefix $(bld_dir)/,$(test_list:%=%.elf))
test_hex := $(addprefix $(bld_dir)/,$(test_list:%=%.hex))
test_dump := $(addprefix $(bld_dir)/,$(test_list:%=%.dump))

CFLAGS := -I$(inc_dir) -DASM -Wa,-march=RV32$(ARCH) -m32 -D__riscv_xlen=32 -D__MACHINE_MODE
LDFLAGS := -static -fvisibility=hidden -nostdlib -nostartfiles -T$(inc_dir)/link.ld

default: $(test_elf) $(test_hex) $(test_dump)

$(bld_dir)/%.o: $(src_dir)%.S $(inc_dir)/riscv_macros.h
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

$(bld_dir)/%.elf: $(bld_dir)/%.o
	$(RISCV_GCC) $^ $(LDFLAGS) -o $@

$(bld_dir)/%.hex: $(bld_dir)/%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/%.dump: $(bld_dir)/%.elf
	$(RISCV_OBJDUMP) $^ > $@

clean:
	$(RM) $(test_elf) $(test_hex) $(test_dump)
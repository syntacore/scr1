src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

FLAGS = -O3 -funroll-loops -fpeel-loops -fgcse-sm -fgcse-las -flto
FLAGS_STR = "$(FLAGS)"

CFLAGS := $(FLAGS) \
-static -m32 -std=gnu99 -fno-common -fno-builtin-printf \
-Wa,-march=RV32$(ARCH) -march=RV32$(ARCH) \
-DFLAGS_STR=\"$(FLAGS_STR)\" \
-DSELF_TIMED=1 -DTIME=1
LDFLAGS := -nostartfiles -nostdlib -lc -lgcc
VPATH += $(src_dir) $(inc_dir)
incs += -I$(src_dir) -I$(inc_dir)

c_src := sc_print.c dhry_1.c dhry_2.c
asm_src := crt.S
c_objs := $(addprefix $(bld_dir)/,$(patsubst %.c, %.o, $(c_src)))
asm_objs := $(addprefix $(bld_dir)/,$(patsubst %.S, %.o, $(asm_src)))

default: $(bld_dir)/dhrystone21.elf $(bld_dir)/dhrystone21.hex $(bld_dir)/dhrystone21.dump

$(bld_dir)/%.o: %.S
	$(RISCV_GCC) $(CFLAGS) -D__ASSEMBLY__=1 -c $(incs) $< -o $@

$(bld_dir)/%.o: %.c
	$(RISCV_GCC) $(CFLAGS) -c $(incs) $< -o $@

$(bld_dir)/dhrystone21.elf: $(inc_dir)/link.ld $(c_objs) $(asm_objs)
	$(RISCV_GCC) -o $@ -T $^ $(LDFLAGS)

$(bld_dir)/dhrystone21.hex: $(bld_dir)/dhrystone21.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/dhrystone21.dump: $(bld_dir)/dhrystone21.elf
	$(RISCV_OBJDUMP) $^ > $@

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/dhrystone21.elf $(bld_dir)/dhrystone21.hex $(bld_dir)/dhrystone21.dump
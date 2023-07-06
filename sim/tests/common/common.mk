ADD_ASM_MACRO ?= -D__ASSEMBLY__=1

FLAGS = -O2 -funroll-loops -fpeel-loops -fgcse-sm -fgcse-las $(ADD_FLAGS)
FLAGS_STR = "$(FLAGS)"

CFLAGS_COMMON = -static -std=gnu99 -fno-common -fno-builtin-printf -DTCM=$(TCM)
CFLAGS_ARCH = -Wa,-march=rv32$(ARCH)_zicsr_zifencei -march=rv32$(ARCH)_zicsr_zifencei -mabi=$(ABI)

CFLAGS := $(FLAGS) $(EXT_CFLAGS) \
$(CFLAGS_COMMON) \
$(CFLAGS_ARCH) \
-DFLAGS_STR=\"$(FLAGS_STR)\" \
$(ADD_CFLAGS)

LDFLAGS   ?= -nostartfiles -nostdlib -lc -lgcc -march=rv32$(ARCH)_zicsr_zifencei -mabi=$(ABI)

ifeq (,$(findstring 0,$(TCM)))
ld_script ?= $(inc_dir)/link_tcm.ld
asm_src   ?= crt_tcm.S
else
ld_script ?= $(inc_dir)/link.ld
asm_src   ?= crt.S
endif

VPATH += $(src_dir) $(inc_dir) $(ADD_VPATH)
incs  += -I$(src_dir) -I$(inc_dir) $(ADD_incs)

c_objs   := $(addprefix $(bld_dir)/,$(patsubst %.c, %.o, $(c_src)))
asm_objs := $(addprefix $(bld_dir)/,$(patsubst %.S, %.o, $(asm_src)))

$(bld_dir)/%.o: %.S
	$(RISCV_GCC) $(CFLAGS) $(ADD_ASM_MACRO) -c $(incs) $< -o $@

$(bld_dir)/%.o: %.c
	$(RISCV_GCC) $(CFLAGS) -c $(incs) $< -o $@

$(bld_dir)/%.elf: $(ld_script) $(c_objs) $(asm_objs)
	$(RISCV_GCC) -o $@ -T $^ $(LDFLAGS)

$(bld_dir)/%.hex: $(bld_dir)/%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/%.dump: $(bld_dir)/%.elf
	$(RISCV_OBJDUMP) -D -w -x -S $^ > $@

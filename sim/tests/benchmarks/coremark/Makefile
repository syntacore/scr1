src_dir := $(dir $(lastword $(MAKEFILE_LIST)))

FLAGS = -O2 -funroll-loops -fpeel-loops -fgcse-sm -fgcse-las
FLAGS_STR = "$(FLAGS)"

CFLAGS := $(FLAGS) $(EXT_CFLAGS) \
-static -std=gnu99 -fno-common -fno-builtin-printf \
-Wa,-march=rv32$(ARCH) -march=rv32$(ARCH) -mabi=$(ABI) \
-DFLAGS_STR=\"$(FLAGS_STR)\"
LDFLAGS := -nostartfiles -nostdlib -lc -lgcc -march=rv32$(ARCH) -mabi=$(ABI)
VPATH += $(src_dir) $(src_dir)/src $(inc_dir)
incs += -I$(src_dir) -I$(src_dir)/src -I$(inc_dir)

ifdef TCM
ld_script := $(inc_dir)/link_tcm.ld
asm_src := crt_tcm.S
else
ld_script := $(inc_dir)/link.ld
asm_src := crt.S
endif

ifeq ("$(ITERATIONS)","")
ITERATIONS=1
endif

CFLAGS += -DITERATIONS=$(ITERATIONS)

c_src := core_portme.c sc_print.c 
coremark_src := ./src/core_list_join.c ./src/core_matrix.c ./src/core_main.c ./src/core_util.c ./src/core_state.c
c_src += core_list_join.c core_matrix.c core_main.c core_util.c core_state.c

c_objs := $(addprefix $(bld_dir)/,$(patsubst %.c, %.o, $(c_src)))
asm_objs := $(addprefix $(bld_dir)/,$(patsubst %.S, %.o, $(asm_src)))


default: check_coremark_src $(bld_dir)/coremark.elf $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 

check_coremark_src:
	@for i in $(coremark_src) ; do \
		if [ ! -f $$i ] ; then \
		    printf "\n\n===========================================================================================\n"; \
		    printf "Source file: $$i not exist!\n"; \
		    printf "Please download CoreMark sources and place it '/coremark/src' directory in this repository\n"; \
		    printf "===========================================================================================\n\n"; \
		    exit 1; \
		fi \
	done


$(bld_dir)/%.o: %.S
	$(RISCV_GCC) $(CFLAGS) -D__ASSEMBLY__=1 -c $(incs) $< -o $@

$(bld_dir)/%.o: %.c
	$(RISCV_GCC) $(CFLAGS) -c $(incs) $< -o $@

$(bld_dir)/coremark.elf: $(ld_script) $(c_objs) $(asm_objs)
	$(RISCV_GCC) -o $@ -T $^ $(LDFLAGS)

$(bld_dir)/coremark.hex: $(bld_dir)/coremark.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/coremark.dump: $(bld_dir)/coremark.elf
	$(RISCV_OBJDUMP) $^ > $@

clean:
	$(RM) $(c_objs) $(asm_objs) $(bld_dir)/coremark.hex $(bld_dir)/coremark.dump 
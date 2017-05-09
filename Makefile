#------------------------------------------------------------------------------
# Makefile for SCR1 riscv-isa-tests
#------------------------------------------------------------------------------
XLEN := 32

# Parameters
ARCH := IMC
RVM := 1
RVC := 1
# Testbench memory delay patterns (FFFFFFFF - no delay, 00000000 - random delay, 00000001 - max delay)
imem_pattern := FFFFFFFF
dmem_pattern := FFFFFFFF

# Paths
src_dir := ${CURDIR}/riscv_isa_tests/src
inc_dir := ${CURDIR}/riscv_isa_tests/includes
bld_dir := ${CURDIR}/riscv_isa_tests/build/

rtl_inc := ${CURDIR}/src/includes
rtl_core := ${CURDIR}/src/core
rtl_primitives := ${CURDIR}/src/core/primitives
rtl_pipeline := ${CURDIR}/src/pipeline
rtl_top := ${CURDIR}/src/top
rtl_tb := ${CURDIR}/src/tb
rtl_bld_dir := ${CURDIR}/build/

test_results := $(rtl_bld_dir)test_results.txt
test_info := $(rtl_bld_dir)test_info

# Environment
CROSS_PREFIX ?= riscv$(XLEN)-unknown-elf-
RISCV_GCC ?= $(CROSS_PREFIX)gcc
RISCV_OBJDUMP ?= $(CROSS_PREFIX)objdump -D
RISCV_OBJCOPY ?= $(CROSS_PREFIX)objcopy -O verilog
RISCV_READELF ?= $(CROSS_PREFIX)readelf -s
CFLAGS += -I$(inc_dir) -DASM -Wa,-march=RV$(XLEN)$(ARCH) -m32
CFLAGS += -D__riscv_xlen=$(XLEN) -D__MACHINE_MODE
LDFLAGS += -static -fvisibility=hidden -nostdlib -nostartfiles -T$(inc_dir)/link.ld

tests_list := 	addi \
				add \
				andi \
				and \
				auipc \
				beq \
				bge \
				bgeu \
				blt \
				bltu \
				bne \
				ebreak \
				ecall \
				fence_i \
				illegal \
				jalr \
				jal \
				lb \
				lbu \
				lh \
				lhu \
				lui \
				lw \
				ma_addr \
				ma_fetch \
				mcsr \
				ori \
				or \
				sb \
				sh \
				simple \
				slli \
				sll \
				slti \
				sltiu \
				slt \
				sltu \
				srai \
				sra \
				srli \
				srl \
				sub \
				sw \
				wfi \
				xori \
				xor \

ifeq ($(RVC),1)
tests_list += rvc
endif
ifeq ($(RVM),1)
tests_list += div divu mulh mulhsu mulhu mul rem remu
endif

tests_elf := $(addprefix $(bld_dir),$(tests_list:%=%.elf))
tests_hex := $(addprefix $(bld_dir),$(tests_list:%=%.hex))
tests_dump := $(addprefix $(bld_dir),$(tests_list:%=%.dump))
tests_noext := $(addprefix $(bld_dir),$(tests_list))


# Build
.PHONY: clean build_vcs build_modelsim run_vcs run_modelsim tests

default: run_modelsim

run_vcs: tests build_vcs
	cd $(rtl_bld_dir) ; \
	printf "" > $(test_results) ; \
	printf "" > $(test_info) ; \
	for i in $(tests_noext) ; do \
		sc_exit=$$( $(RISCV_READELF) $$i.elf | grep -w "sc_exit" | awk '{ print $$2 }' ) ; \
		printf "%s.hex\t%s\n" "$$i" "$$sc_exit" >> $(test_info) ; \
	done ; \
	$(rtl_bld_dir)simv \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern)

run_modelsim: tests build_modelsim
	cd $(rtl_bld_dir) ; \
	printf "" > $(test_results) ; \
	printf "" > $(test_info) ; \
	for i in $(tests_noext) ; do \
		sc_exit=$$( $(RISCV_READELF) $$i.elf | grep -w "sc_exit" | awk '{ print $$2 }' ) ; \
		printf "%s.hex\t%s\n" "$$i" "$$sc_exit" >> $(test_info) ; \
	done ; \
	vsim -c -do "run -all" +nowarn3691 \
	+test_info=$(test_info) \
	+test_results=$(test_results) \
	+imem_pattern=$(imem_pattern) \
	+dmem_pattern=$(dmem_pattern) \
	work.scr1_top_tb


build_vcs: $(rtl_bld_dir)
	cd $(rtl_bld_dir); \
	vcs \
	-full64                             \
    -lca                                \
    -sverilog                           \
    -notice                             \
    +lint=all,noVCDE                    \
    -timescale=1ns/1ps               	\
    +incdir+$(rtl_inc)                 	\
    -nc                                 \
    -debug_all                          \
    $(rtl_core)/*.sv 					\
    $(rtl_primitives)/*.sv 				\
    $(rtl_pipeline)/*.sv 				\
    $(rtl_tb)/*.sv 						\
    $(rtl_top)/*.sv

build_modelsim: $(rtl_bld_dir)
	cd $(rtl_bld_dir); \
	vlib work; \
	vmap work work; \
	vlog -work work -O0 -mfcu -sv +incdir+$(rtl_inc) \
	$(rtl_core)/*.sv 					\
	$(rtl_primitives)/*.sv 				\
	$(rtl_pipeline)/*.sv 				\
	$(rtl_tb)/*.sv 						\
	$(rtl_top)/*.sv


tests: $(tests_hex) $(tests_dump) $(tests_elf)

$(bld_dir):
	mkdir -p $@

$(rtl_bld_dir):
	mkdir -p $@

$(bld_dir)%.o: $(src_dir)/%.S | $(bld_dir)
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

$(bld_dir)%.elf: $(bld_dir)%.o
	$(RISCV_GCC) $^ $(LDFLAGS) -o $@

$(bld_dir)%.hex: $(bld_dir)%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)%.dump: $(bld_dir)%.elf
	$(RISCV_OBJDUMP) $^ > $@

clean:
	rm -r $(bld_dir) $(rtl_bld_dir)
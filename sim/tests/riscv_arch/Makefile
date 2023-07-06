## @file
## Syntacore SCR* tests
##
## @copyright 2015-2018 Syntacore. All rights reserved.
## RISCV-Compliance
##

XLEN ?= 32
ABI  ?= ilp32
ARCH ?=im
override ARCH :=rv$(XLEN)$(ARCH)

$(info >>> ARCH := $(ARCH))

src_dir       := $(CURDIR)
RISCV_ARCH_TESTS := $(src_dir)/../../../dependencies/riscv-arch/

#I IM IMC IC
#EM EMC EC

ifeq (e,$(findstring e, $(ARCH)))
    ifeq (e,$(findstring e,$(ARCH)))
        $(info >>> E32 TESTS)
        included_e    += $(filter %.S,\
                             $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/E/src/*))
        arch_set      += $(included_e)
        reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/E/*/*.reference_output)
    endif
    ifeq (c,$(findstring c,$(ARCH)))
        $(info >>> EC32 TESTS)
        included_ec   += $(filter %.S,\
                             $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/C/src/*))
        arch_set      += $(included_ec)
        reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/C/*/*.reference_output)
    endif
    ifeq (m,$(findstring m,$(ARCH)))
        $(info >>> EM32 TESTS)
        included_em   += $(filter %.S,\
                             $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/M/src/*))
        arch_set      += $(included_em)
        reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32e_unratified/M/*/*.reference_output)
    endif
else ## ifdef SCR_BASE_RVE_EXT
    ifeq (i,$(findstring i, $(ARCH)))
        ifeq (i,$(findstring i,$(ARCH)))
            $(info >>> I32 TESTS)
            included_i    += $(filter %.S,\
                                 $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/I/src/*))
            included_ip   += $(filter %.S,\
                                 $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/privilege/src/*))
            included_i    += $(filter %.S,\
                                 $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/Zifencei/src/*))
            included_i    += $(included_ip)
            arch_set      += $(included_i)
            reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/I/*/*.reference_output)
            reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/privilege/*/*.reference_output)
            reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/Zifencei/*/*.reference_output)
        endif
        ifeq (c,$(findstring c,$(ARCH)))
            $(info >>> IC32 TESTS)
            included_ic   += $(filter %.S,\
                                 $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/C/src/*))
            arch_set      += $(included_ic)
            reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/C/*/*.reference_output)
        endif
        ifeq (m,$(findstring m,$(ARCH)))
            $(info >>> IM32 TESTS)
            included_im   += $(filter %.S,\
                                 $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/M/src/*))
            arch_set      += $(included_im)
            reference_src += $(wildcard $(RISCV_ARCH_TESTS)/riscv-test-suite/rv32i_m/M/*/*.reference_output)
        endif
    endif
endif


$(info >>>$(ARCH) set included)

ifeq ($(arch_set),)
$(info >>> No arch tests included)
endif

$(info >>>>> arch set: $(arch_set))

dst_dir              := $(bld_dir)
test_name            := riscv_arch
bld_dir              := $(addprefix $(dst_dir)/, $(test_name))
obj_dir              := $(bld_dir)/riscv_arch_objs

ifeq ($(ARCH),$(filter $(ARCH),rv32im))
cut_list             += misalign-blt-01 misalign-jal-01 misalign-beq-01 misalign2-jalr-01 misalign-bgeu-01 misalign-bltu-01 misalign-bge-01 misalign-bne-01 # privilege test used mtvec
endif
ifeq ($(ARCH),$(filter $(ARCH),rv32ic))
cut_list             += misalign-lw-01 misalign-sh-01 misalign-lhu-01 misalign-lh-01 ecall misalign-sw-01 # privilege test used mtvec
endif

cut_list             += bne-01 blt-01 beq-01 bge-01 jal-01 bltu-01 bgeu-01 # i - base
cut_list             += ebreak cebreak-01 cswsp-01 # C - base
testnames            := $(basename $(notdir $(arch_set)))
filtered             := $(filter-out $(cut_list),$(testnames))
objs                 := $(addprefix $(bld_dir)/,$(filtered:%=%.o))
test_elf             := $(addprefix $(dst_dir)/arch_,$(filtered:%=%.elf))
test_hex             := $(addprefix $(dst_dir)/arch_,$(filtered:%=%.hex))
test_dump            := $(addprefix $(bld_dir)/arch_,$(filtered:%=%.dump))

arch_macros_file := $(root_dir)/sim/tests/riscv_arch/model_test.h
arch_output ?= true

ifeq (e,$(findstring e,$(ARCH)))
    EXT_CFLAGS += -DRVTEST_E
endif

# Set name file for RV32I
testnames_i     := $(basename $(notdir $(included_i)))
testnames_im     := $(basename $(notdir $(included_im)))
testnames_ic      := $(basename $(notdir $(included_ic)))
testnames_ib       := $(basename $(notdir $(included_ib)))
filtered_i      := $(filter-out $(cut_list),$(testnames_i))
filtered_im      := $(filter-out $(cut_list),$(testnames_im))
filtered_ic       := $(filter-out $(cut_list),$(testnames_ic))
filtered_ib        := $(filter-out $(cut_list),$(testnames_ib))

# Set name file for RVE
testnames_e     := $(basename $(notdir $(included_e)))
testnames_em     := $(basename $(notdir $(included_em)))
testnames_ec      := $(basename $(notdir $(included_ec)))
filtered_e      := $(filter-out $(cut_list),$(testnames_e))
filtered_em      := $(filter-out $(cut_list),$(testnames_em))
filtered_ec       := $(filter-out $(cut_list),$(testnames_ec))

CFLAGS := -I$(inc_dir) -I$(src_dir) -DASM -mabi=$(ABI) $(EXT_CFLAGS) -DXLEN=$(XLEN) -D__riscv_xlen=$(XLEN) -w
LDFLAGS := -static -fvisibility=hidden -nostdlib -nostartfiles -T$(inc_dir)/link.ld -march=$(ARCH) -mabi=$(ABI)
GCCVERSIONGT7 := $(shell expr `$(RISCV_GCC) -dumpfullversion | cut -f1 -d'.'` \> 7)
ifeq "$(GCCVERSIONGT7)" "1"
	LDFLAGS += -mno-relax
endif
VPATH += $(src_dir) $(bld_dir) $(obj_dir) $(asm_path) $(ref_path) $(RISCV_ARCH_TESTS)

ifeq ($(arch_output), true)
CFLAGS += -D_ARCH_OUTPUT
endif

default: clean log_requested_tgt check_version cp_asm ref_data $(test_elf) $(test_hex) $(test_dump)

define compile_template
$(obj_dir)/$(1).o: $(obj_dir) cp_asm
	$(RISCV_GCC) -c $$(bld_dir)/arch_asm/$(1).S $$(CFLAGS) -Wa,$(2) $(2) -o $$@
endef

define preprocessing
for test_asm in $(1); do                                                  \
march_tmp=$$test_asm ;                                                    \
march_tmp=$${march_tmp%/src*} ;                                           \
march_tmp=$$(basename $$march_tmp) ;                                      \
file_name="$$(basename $${test_asm})" ;                                   \
$(RISCV_GCC) $(CFLAGS) -Wa,$(2) $(2) -E $$test_asm                        \
-o $(bld_dir)/arch_asm/$$file_name ;                                      \
done
endef

define preprocessing_privilege
for test_asm in $(1); do                                                       \
march_tmp=$$test_asm ;                                                         \
march_tmp=$${march_tmp%/src*} ;                                                \
march_tmp=$$(basename $$march_tmp) ;                                           \
file_name="$$(basename $${test_asm})" ;                                        \
$(RISCV_GCC) $(CFLAGS) -Drvtest_mtrap_routine=True -Dmhandler -Wa,$(2) $(2) -E $$test_asm \
-o $(bld_dir)/arch_asm/$$file_name ;                                           \
done
endef

$(foreach SRC,$(filtered_i),$(eval $(call compile_template,$(SRC),-march=rv32i_zicsr_zifencei)))
$(foreach SRC,$(filtered_im),$(eval $(call compile_template,$(SRC),-march=rv32im_zicsr_zifencei)))
$(foreach SRC,$(filtered_ic),$(eval $(call compile_template,$(SRC),-march=rv32ic_zicsr_zifencei)))

$(foreach SRC,$(filtered_e),$(eval $(call compile_template,$(SRC),-march=rv32e_zicsr_zifencei)))
$(foreach SRC,$(filtered_em),$(eval $(call compile_template,$(SRC),-march=rv32em_zicsr_zifencei)))
$(foreach SRC,$(filtered_ec),$(eval $(call compile_template,$(SRC),-march=rv32ec_zicsr_zifencei)))

log_requested_tgt: $(bld_dir)
	$(foreach test_name, $(filtered), $(eval $(shell echo arch_$(test_name).hex >> $(bld_dir)/../test_info)))

$(bld_dir) :
	mkdir -p $(bld_dir)

$(obj_dir) : | ref_data
	mkdir -p $(obj_dir)

$(dst_dir)/arch_%.elf: $(obj_dir)/%.o | $(dep_files)
	$(RISCV_GCC) $^ $(LDFLAGS) -o $@ -g

$(dst_dir)/arch_%.hex: $(dst_dir)/arch_%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/arch_%.dump: $(dst_dir)/arch_%.elf
	$(RISCV_OBJDUMP) -D -w -x -S $^ > $@

ref_data:
	mkdir -p $(bld_dir)/ref_data
	for files in $(reference_src) ; do \
	sed_input=$$files ; \
	sed_output=$$(basename $${files%.*}) ; \
	sed "s/\r$$//; \
	s/\(........\)/\1,/g; \
	s/.$$//; s/\(.*\),\(.*\),\(.*\),\(.*\)/\4,\3,\2,\1/;" \
    $$sed_input > $(bld_dir)/ref_data/$$sed_output; \
	done

cp_asm:
	mkdir -p $(bld_dir)/arch_asm
	$(call preprocessing,$(included_i),-march=rv32i)
	$(call preprocessing_privilege,$(included_ip),-march=rv32i)
	$(call preprocessing,$(included_im),-march=rv32im)
	$(call preprocessing,$(included_ic),-march=rv32ic)
	$(call preprocessing,$(included_e),-march=rv32e)
	$(call preprocessing,$(included_em),-march=rv32em)
	$(call preprocessing,$(included_ec),-march=rv32ec)

riscv_arch_tests_dir    := $(if $(RISCV_ARCH_TESTS), $(RISCV_ARCH_TESTS), ./undefined)
riscv_tests_commit      := 9141cf9274b610d059199e8aa2e21f54a0bc6a6e
## commit hash readed from local copy of https://github.com/riscv/riscv-arch-test.git
tmp_commit     = $(shell cd $(riscv_arch_tests_dir) 2>/dev/null && git log -1 | grep "commit" | cut -f2 -d ' ')
is_commit_good = $(if $(subst $(riscv_tests_commit),,$(tmp_commit)),false,true)

# Color
RED=\033[0;31m
NC=\033[0m

check_version : $(riscv_arch_tests_dir)
	@if [ ! -d $(riscv_arch_tests_dir) ]; then \
		echo -e "$(RED)==========================================================================" &&\
		echo "   Error! Environment variable RISCV_ARCH_TESTS='$(riscv_arch_tests_dir)' " &&\
		echo "      directory not exist!" && \
		echo "==========================================================================$(NC)" ; \
	fi
ifneq ($(is_commit_good),true)
	@echo -e "$(RED)=========================================================================="
	@echo "   Warning! Execution of test code is not guaranteed "
	@echo "   while using the current commit of repository located at : $(riscv_arch_tests_dir) ."
	@echo "   "
	@echo "   riscv_arch repository must point to commit $(riscv_tests_commit)!"
	@echo -e "==========================================================================$(NC)"
endif

$(riscv_arch_tests_dir) :.
ifndef RISCV_ARCH_TESTS
	@echo -e "$(RED)=========================================================================="
	@echo "    Error! Environment variable RISCV_ARCH_TESTS not set!"
	@echo "    You must set the environment variable RISCV_ARCH_TESTS"
	@echo "    The variable should point to the local copy of the"
	@echo "      repository https://github.com/riscv/riscv-arch-test.git"
	@echo "      with the commit $(riscv_tests_commit)"
	@echo -e "==========================================================================$(NC)"
	exit 1
endif

clean:
	$(RM) -R $(test_elf) $(test_hex) $(bld_dir)

.PHONY: check_version clean ref_data cp_asm default

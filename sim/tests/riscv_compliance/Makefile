## @file
## Syntacore SCR* tests
##
## @copyright 2015-2018 Syntacore. All rights reserved.
## RISCV-Compliance
##

ARCH ?=im
override ARCH:=rv32$(ARCH)

src_dir       := $(CURDIR)
RISCV_COMPLIANCE_TESTS := $(src_dir)/../../../dependencies/riscv-compliance/

#I IM IMC IC
#EM EMC EC

ifeq (rv32e,$(findstring rv32e,$(ARCH)))
    $(info >>> RV32E - no compliance tests)
else ## ifdef SCR_BASE_RVE_EXT
  #ifeq (rv32i,$(findstring rv32i,$(ARCH)))
  ifeq ($(ARCH),$(filter $(ARCH),rv32i rv32im rv32imc rv32ic))
    $(info >>> I32 TESTS)
    included_i += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32i/src/*))
	included_i += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32Zicsr/src/*))
	included_i += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32Zifencei/src/*))
    compliance_set += $(included_i)
  endif

  #$(if or ifeq(rv32im,$(findstring rv32im,$(ARCH))), (rv32imc,$(findstring rv32imc,$(ARCH))))
  ifeq ($(ARCH),$(filter $(ARCH), rv32im rv32imc))
    $(info >>> IM32 TESTS)
    included_im += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32im/src/*))
    compliance_set += $(included_im)
  endif ##

  ifeq (rv32imc,$(findstring rv32imc,$(ARCH)))
    $(info >>> IMC32 TESTS)
    included_imc += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32imc/src/*))
    compliance_set += $(included_imc)
  endif ## ifeq (rv32imc,$(findstring rv32imc,$(ARCH)))
  ifeq (rv32ic,$(findstring rv32ic,$(ARCH)))
  endif
endif ##


$(info >>>$(ARCH) set included)

ifeq ($(compliance_set),)
$(info >>> No compliance tests included)
endif

$(info >>>>> compliance set: $(compliance_set))

dst_dir       := $(bld_dir)
test_name     := riscv_compliance
bld_dir       := $(addprefix $(dst_dir)/, $(test_name))
obj_dir       := $(bld_dir)/riscv_compliance_objs

#cut_list      += scall csr shamt simple
cut_list += I-MISALIGN_JMP-01 I-MISALIGN_LDST-01 I-EBREAK-01 I-ECALL-01
reference_src += $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32i*/*/*.reference_output)
reference_src += $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32Zi*/*/*.reference_output)
testnames     := $(basename $(notdir $(compliance_set)))
filtered      := $(filter-out $(cut_list),$(testnames))
objs          := $(addprefix $(bld_dir)/,$(filtered:%=%.o))
test_elf      := $(addprefix $(dst_dir)/compliance_,$(filtered:%=%.elf))
test_hex      := $(addprefix $(dst_dir)/compliance_,$(filtered:%=%.hex))
test_dump     := $(addprefix $(bld_dir)/compliance_,$(filtered:%=%.dump))

compliance_macros_file := $(root_dir)/sim/tests/riscv_compliance/compliance_io.h
compliance_output ?= true

testnames_i     := $(basename $(notdir $(included_i)))
testnames_im     := $(basename $(notdir $(included_im)))
testnames_imc     := $(basename $(notdir $(included_imc)))
filtered_i      := $(filter-out $(cut_list),$(testnames_i))
filtered_im      := $(filter-out $(cut_list),$(testnames_im))
filtered_imc      := $(filter-out $(cut_list),$(testnames_imc))

# ARCH_FLAGS := -Wa,-march=rv32im -march=rv32im
# ARCH_FLAGS_C := -Wa,-march=rv32imc -march=rv32imc
CFLAGS := -I$(inc_dir) -I$(src_dir) -DASM -mabi=ilp32 -D__riscv_xlen=32 -w
LDFLAGS := -static -fvisibility=hidden -nostdlib -nostartfiles -T$(inc_dir)/link.ld -march=$(ARCH) -mabi=ilp32
GCCVERSIONGT7 := $(shell expr `$(RISCV_GCC) -dumpfullversion | cut -f1 -d'.'` \> 7)
ifeq "$(GCCVERSIONGT7)" "1"
	LDFLAGS += -mno-relax
endif
VPATH += $(src_dir) $(bld_dir) $(obj_dir) $(asm_path) $(ref_path) $(RISCV_COMPLIANCE_TESTS)

ifeq ($(compliance_output), true)
CFLAGS += -D_COMPLIANCE_OUTPUT
endif

default: clean log_requested_tgt check_version cp_asm ref_data $(test_elf) $(test_hex) $(test_dump)

define compile_template
$(obj_dir)/$(1).o: $(obj_dir) cp_asm
	$(RISCV_GCC) -c $$(bld_dir)/compliance_asm/$(1).S $$(CFLAGS) -Wa,$(2) $(2) -o $$@
endef

define preprocessing
for test_asm in $(1); do                                                  \
march_tmp=$$test_asm ;                                                    \
march_tmp=$${march_tmp%/src*} ;                                           \
march_tmp=$$(basename $$march_tmp) ;                                      \
file_name="$$(basename $${test_asm})" ;                                   \
$(RISCV_GCC) $(CFLAGS) -Wa,$(2) $(2) -E $$test_asm                        \
-o $(bld_dir)/compliance_asm/$$file_name ;                                \
done
endef

$(foreach SRC,$(filtered_i),$(eval $(call compile_template,$(SRC),-march=rv32i)))
$(foreach SRC,$(filtered_im),$(eval $(call compile_template,$(SRC),-march=rv32im)))
$(foreach SRC,$(filtered_imc),$(eval $(call compile_template,$(SRC),-march=rv32imc)))


log_requested_tgt: $(bld_dir)
	$(foreach test_name, $(filtered), $(eval $(shell echo compliance_$(test_name).hex >> $(bld_dir)/../test_info)))

$(bld_dir) :
	mkdir -p $(bld_dir)

$(obj_dir) : | ref_data
	mkdir -p $(obj_dir)

$(dst_dir)/compliance_%.elf: $(obj_dir)/%.o | $(dep_files)
	$(RISCV_GCC) $^ $(LDFLAGS) -o $@ -g

$(dst_dir)/compliance_%.hex: $(dst_dir)/compliance_%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/compliance_%.dump: $(dst_dir)/compliance_%.elf
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
	mkdir -p $(bld_dir)/compliance_asm
	$(call preprocessing,$(included_i),-march=rv32i)
	$(call preprocessing,$(included_im),-march=rv32im)
	$(call preprocessing,$(included_imc),-march=rv32imc)


riscv_compliance_tests_dir    := $(if $(RISCV_COMPLIANCE_TESTS), $(RISCV_COMPLIANCE_TESTS), ./undefined)
riscv_tests_commit := d51259b2a949be3af02e776c39e135402675ac9b
## commit hash readed from local copy of https://github.com/riscv/riscv-compliance
tmp_commit = $(shell cd $(riscv_compliance_tests_dir) 2>/dev/null && git log -1 | grep "commit" | cut -f2 -d ' ')
is_commit_good = $(if $(subst $(riscv_tests_commit),,$(tmp_commit)),false,true)

# Color
RED=\033[0;31m
NC=\033[0m

check_version : $(riscv_compliance_tests_dir)
	@if [ ! -d $(riscv_compliance_tests_dir) ]; then \
		echo -e "$(RED)==========================================================================" &&\
		echo "   Error! Environment variable RISCV_COMPLIANCE_TESTS='$(riscv_compliance_tests_dir)' " &&\
		echo "      directory not exist!" && \
		echo "==========================================================================$(NC)" ; \
	fi
ifneq ($(is_commit_good),true)
	@echo -e "$(RED)=========================================================================="
	@echo "   Warning! Execution of test code is not guaranteed "
	@echo "   while using the current commit of repository located at : $(riscv_compliance_tests_dir) ."
	@echo "   "
	@echo "   riscv_compliance repository must point to commit $(riscv_tests_commit)!"
	@echo -e "==========================================================================$(NC)"
endif

$(riscv_compliance_tests_dir) :.
ifndef RISCV_COMPLIANCE_TESTS
	@echo -e "$(RED)=========================================================================="
	@echo "    Error! Environment variable RISCV_COMPLIANCE_TESTS not set!"
	@echo "    You must set the environment variable RISCV_COMPLIANCE_TESTS"
	@echo "    The variable should point to the local copy of the"
	@echo "      repository https://github.com/riscv/riscv-compliance"
	@echo "      with the commit $(riscv_tests_commit)"
	@echo -e "==========================================================================$(NC)"
	exit 1
endif

clean:
	$(RM) -R $(test_elf) $(test_hex) $(bld_dir)

.PHONY: check_version clean ref_data cp_asm default

## @file
## Syntacore SCR* tests
##
## @copyright 2015-2018 Syntacore. All rights reserved.
## RISCV-Compliance
##

ARCH ?=im
override ARCH:=rv32$(ARCH)

#I IM IMC IC 
#EM EMC EC

ifeq (rv32e,$(findstring rv32e,$(ARCH)))
    $(info >>> RV32E - no compliance tests)
else ## ifdef SCR_BASE_RVE_EXT
  #ifeq (rv32i,$(findstring rv32i,$(ARCH)))
  ifeq ($(ARCH),$(filter $(ARCH),rv32i rv32im rv32imc rv32ic))
    $(info >>> I32 TESTS)
    included += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32i/src/*))
    $(info >>> UI32 TESTS)
    included += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32ui/src/*))
  endif
  ifeq ($(ARCH),$(filter $(ARCH),rv32im rv32imc))
    $(info >>> M32 TESTS)
    included += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32mi/src/*))
  endif ## ifeq ($(ARCH),$(filter $(ARCH),rv32i rv32im rv32imc rv32ic))

  #$(if or ifeq(rv32im,$(findstring rv32im,$(ARCH))), (rv32imc,$(findstring rv32imc,$(ARCH))))
  ifeq ($(ARCH),$(filter $(ARCH), rv32im))
    $(info >>> IM32 TESTS)
    included += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32im/src/*))
  endif ## 

  ifeq (rv32imc,$(findstring rv32imc,$(ARCH)))
    $(info >>> IMC32 TESTS)
    included_c += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32imc/src/*))
  endif ## ifeq (rv32imc,$(findstring rv32imc,$(ARCH)))

  #ifeq $(or (rv32imc,$(findstring rv32imc,$(ARCH))), (rv32ic,$(findstring rv32ic,$(ARCH))))
  ifeq ($(ARCH),$(filter $(ARCH), rv32ic rv32imc))
   $(info >>> UC32 TESTS)
   included_c += $(filter %.S,\
                        $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/rv32uc/src/*))
  endif ## ifdef 

endif ## 


compliance_set += $(included)

$(info >>>$(ARCH) set included)
ifeq ($(compliance_set),)
$(info >>> No compliance tests included)
endif

$(info >>>>> compliance set: $(compliance_set))

dst_dir       := $(root_dir)/build
test_name     := riscv_compliance
bld_dir       := $(addprefix $(dst_dir)/, $(test_name))
src_dir       := $(CURDIR)
obj_dir       := $(bld_dir)/riscv_compliance_objs
cut_list      := I-EBREAK-01 I-ECALL-01 I-MISALIGN_JMP-01 I-MISALIGN_LDST-01
cut_list      += scall csr shamt simple
reference_src := $(wildcard $(RISCV_COMPLIANCE_TESTS)/riscv-test-suite/*/*/*.reference_output)
testnames     := $(basename $(notdir $(compliance_set)))
filtered      := $(filter-out $(cut_list),$(testnames))
objs          := $(addprefix $(bld_dir)/,$(filtered:%=%.o))
test_elf      := $(addprefix $(dst_dir)/compliance_,$(filtered:%=%.elf))
test_hex      := $(addprefix $(dst_dir)/compliance_,$(filtered:%=%.hex))
test_dump     := $(addprefix $(bld_dir)/compliance_,$(filtered:%=%.dump))

compliance_macros_file := $(root_dir)/sim/tests/riscv_compliance/compliance_io.h
compliance_output ?= true

ARCH_FLAGS := -Wa,-march=rv32im -march=rv32im 
ARCH_FLAGS_C := -Wa,-march=rv32imc -march=rv32imc
CFLAGS := -I$(inc_dir) -I$(src_dir) -DASM -mabi=ilp32 -D__riscv_xlen=32 -w
LDFLAGS := -static -fvisibility=hidden -nostdlib -nostartfiles -T$(inc_dir)/link.ld -march=$(ARCH) -mabi=ilp32
VPATH += $(src_dir) $(bld_dir) $(obj_dir) $(asm_path) $(ref_path) $(RISCV_COMPLIANCE_TESTS)

change = $(shell    cp $(src_dir)/check.c $(2)/$(1).c; \
                    sed -i '6i \#include \"x\"' $(2)/$(1).c; \
                    sed -i '7d' $(2)/$(1).c; \
                    sed -i "6s@x@$(1)@" $(2)/$(1).c )

ifeq ($(compliance_output), true)
CFLAGS += -D_COMPLIANCE_OUTPUT
endif

default: clean check_version cp_asm ref_data ref_code $(test_elf) $(test_hex) $(test_dump)

define compile_template
$(obj_dir)/$$(SRC).o: ref_code
	$(RISCV_GCC) -c $$(bld_dir)/compliance_asm/$(SRC).S $$(CFLAGS) $$(ARCH_FLAGS) -o $$@
	$(RISCV_GCC) -c $$(bld_dir)/ref_code/$(SRC).c $$(CFLAGS) $$(ARCH_FLAGS) -g -I$$(bld_dir)/ref_data/ -o $(addprefix $(bld_dir)/ref_obj/,$(addsuffix .o, $(SRC)))
 endef

$(foreach SRC,$(filtered),$(eval $(compile_template)))

ref_code: | $(obj_dir) cp_asm
	$(foreach SRC,$(compliance_set),$(call change,$(basename $(notdir $(SRC))),$(bld_dir)/ref_code))

$(bld_dir) :
	mkdir -p $(bld_dir)

$(obj_dir) : | ref_data
	mkdir -p $(obj_dir)

$(dst_dir)/compliance_%.elf: $(obj_dir)/%.o | $(dep_files)
	$(RISCV_GCC) $^ $(bld_dir)/ref_obj/$*.o $(LDFLAGS) -o $@ -g

$(dst_dir)/compliance_%.hex: $(dst_dir)/compliance_%.elf
	$(RISCV_OBJCOPY) $^ $@

$(bld_dir)/compliance_%.dump: $(dst_dir)/compliance_%.elf
	$(RISCV_OBJDUMP) -D -w -x -S $^ > $@

ref_data:
	mkdir -p $(bld_dir)/ref_data
	mkdir -p $(bld_dir)/ref_code
	mkdir -p $(bld_dir)/ref_obj
	for files in $(reference_src) ; do \
	sed_input=$$files ; \
	sed_output=$$(basename $${files%.*}) ; \
	sed "s/\r$$//; \
	s/\(........\)/\1,/g; \
	s/.$$//; s/\(.*\),\(.*\),\(.*\),\(.*\)/\4,\3,\2,\1/; \
	s/\(.........\)/\10x/g; s/^/0x/; s/$$/,/; $$ s/.$$//" $$sed_input > $(bld_dir)/ref_data/$$sed_output; \
	done

cp_asm:
	mkdir -p $(bld_dir)/compliance_asm
	for test_asm in $(compliance_set); do \
	march_tmp=$$test_asm ;                                                    \
	march_tmp=$${march_tmp%/src*} ;                                           \
	march_tmp=$$(basename $$march_tmp) ;                                      \
	file_name="$$(basename $${test_asm})" ;          \
	$(RISCV_GCC) $(CFLAGS) $(ARCH_FLAGS) -E $$test_asm                                      \
	-o $(bld_dir)/compliance_asm/$$file_name ;                                \
	done

riscv_compliance_tests_dir    := $(if $(RISCV_COMPLIANCE_TESTS), $(RISCV_COMPLIANCE_TESTS), ./undefined)
riscv_tests_commit := 9f280717f26f50833357db9bfb77a8c79835f162
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
ifneq (,$(is_repo_changed))
	@echo -e "$(RED)=========================================================================="
	@echo "   Error! Repo '$(riscv_compliance_tests_dir)' "
	@echo "     must be unchanged!"
	@echo -e "==========================================================================$(NC)"
	exit 1
endif
ifneq ($(is_commit_good),true)
	@echo -e "$(RED)=========================================================================="
	@echo "   Error! riscv compliance tests must point to commit $(riscv_tests_commit)"
	@echo -e "==========================================================================$(NC)"
	exit 1
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

.PHONY: check_version clean ref_data ref_code cp_asm default

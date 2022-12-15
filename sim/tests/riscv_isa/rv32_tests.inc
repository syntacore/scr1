
ARCH_lowercase = $(shell echo $(ARCH) | tr A-Z a-z)


rv32_isa_tests += isa/rv32mi/illegal.S


ifneq (,$(findstring m,$(ARCH_lowercase)))
rv32_isa_tests += isa/rv32um/div.S      \
              isa/rv32um/divu.S         \
              isa/rv32um/mul.S          \
              isa/rv32um/mulh.S         \
              isa/rv32um/mulhsu.S       \
              isa/rv32um/mulhu.S        \
              isa/rv32um/rem.S          \
              isa/rv32um/remu.S
endif ## ifeq (m,$(findstring m,$(ARCH_lowercase)))

ifneq (,$(findstring c,$(ARCH_lowercase)))
rv32_isa_tests += isa/rv32uc/rvc.S
endif ## ifeq (m,$(findstring c,$(ARCH_lowercase)))
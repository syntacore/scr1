
ARCH_lowercase = $(shell echo $(ARCH) | tr A-Z a-z)


rv32_isa_tests += isa/rv32ui/add.S      \
              isa/rv32ui/addi.S         \
              isa/rv32ui/and.S          \
              isa/rv32ui/andi.S         \
              isa/rv32ui/auipc.S        \
              isa/rv32ui/beq.S          \
              isa/rv32ui/bge.S          \
              isa/rv32ui/bgeu.S         \
              isa/rv32ui/blt.S          \
              isa/rv32ui/bltu.S         \
              isa/rv32ui/bne.S          \
              isa/rv32mi/csr.S          \
              isa/rv32ui/fence_i.S      \
              isa/rv32mi/illegal.S      \
              isa/rv32ui/jal.S          \
              isa/rv32ui/jalr.S         \
              isa/rv32ui/lb.S           \
              isa/rv32ui/lbu.S          \
              isa/rv32ui/lh.S           \
              isa/rv32ui/lhu.S          \
              isa/rv32ui/lui.S          \
              isa/rv32ui/lw.S           \
              isa/rv32mi/ma_addr.S      \
              isa/rv32mi/ma_fetch.S     \
              isa/rv32mi/mcsr.S         \
              isa/rv32ui/or.S           \
              isa/rv32ui/ori.S          \
              isa/rv32ui/sb.S           \
              isa/rv32mi/sbreak.S       \
              isa/rv32mi/scall.S        \
              isa/rv32ui/sh.S           \
              isa/rv32mi/shamt.S        \
              isa/rv32ui/simple.S       \
              isa/rv32ui/sll.S          \
              isa/rv32ui/slli.S         \
              isa/rv32ui/slt.S          \
              isa/rv32ui/slti.S         \
              isa/rv32ui/sltiu.S        \
              isa/rv32ui/sltu.S         \
              isa/rv32ui/sra.S          \
              isa/rv32ui/srai.S         \
              isa/rv32ui/srl.S          \
              isa/rv32ui/srli.S         \
              isa/rv32ui/sub.S          \
              isa/rv32ui/sw.S           \
              isa/rv32ui/xor.S          \
              isa/rv32ui/xori.S

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
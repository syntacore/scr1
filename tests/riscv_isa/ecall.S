# See LICENSE for license details.

#*****************************************************************************
# ecall.S
#-----------------------------------------------------------------------------
#
# Test syscall trap.
#


#include "riscv_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

#ifdef __MACHINE_MODE
  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define sepc mepc
  #define sret eret
  #define stvec_handler mtvec_handler
#endif

  li TESTNUM, 2
  ecall
  j fail

  j pass

  TEST_PASSFAIL

stvec_handler:
  li t1, CAUSE_MACHINE_ECALL
  csrr t0, scause
  bne t0, t1, fail
  csrr t0, sepc
  addi t0, t0, 8
  csrw sepc, t0
  sret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END

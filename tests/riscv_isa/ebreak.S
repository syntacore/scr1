# See LICENSE for license details.

#*****************************************************************************
# ebreak.S
#-----------------------------------------------------------------------------
#
# Test software breakpoint trap.
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

  ebreak
  j fail

  TEST_PASSFAIL

  .align 2
stvec_handler:
  li t1, CAUSE_BREAKPOINT
  csrr t0, scause
  bne t0, t1, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END

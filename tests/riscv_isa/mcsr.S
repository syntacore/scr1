# See LICENSE for license details.

#*****************************************************************************
# mcsr.S
#-----------------------------------------------------------------------------
#
# Test various M-mode CSRs.
#


#include "riscv_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # Check that mcpuid reports the correct XLEN
  TEST_CASE(2, a0, 0x0, csrr a0, mcpuid; srl a0, a0, 30)

  # Check that mhartid reports 0
  TEST_CASE(3, a0, 0x0, csrr a0, mhartid)

  # Check that reading the following CSRs doesn't cause an exception
  csrr a0, mimpid

  # Check that writing the following CSRs doesn't cause an exception
  li t0, 0
  csrs mtvec, t0
  csrs mepc, t0

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END

# See LICENSE for license details.

#*****************************************************************************
# wfi.S
#-----------------------------------------------------------------------------
#
# Test wait-for-interrupt instruction.
#


#include "riscv_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # Make sure wfi doesn't halt the hart, even if interrupts are disabled
  csrc mstatus, MSTATUS_IE
  csrs mie, MIP_SSIP
  csrs mip, MIP_SSIP
  csrw mtime, zero
  csrwi mtimecmp, 100
  wfi

  RVTEST_PASS

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END

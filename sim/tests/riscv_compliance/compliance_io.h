// RISC-V Compliance IO Test Header File

/*
 * Copyright (c) 2005-2018 Imperas Software Ltd., www.imperas.com
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

#ifndef _COMPLIANCE_IO_H
#define _COMPLIANCE_IO_H

//-----------------------------------------------------------------------
// RV IO Macros (Non functional)
//-----------------------------------------------------------------------
#ifdef _COMPLIANCE_OUTPUT

#define RVTEST_IO_PUSH(_SP)                                             \
la _SP, begin_regstate;                                                 \
sw x3, 0(_SP);                                                          \
sw x4, 4(_SP);                                                          \
sw x5, 8(_SP);

#define RVTEST_IO_POP(_SP)                                              \
la _SP, begin_regstate;                                                 \
lw x3, 0(_SP);                                                          \
lw x4, 4(_SP);                                                          \
lw x5, 8(_SP);	

#define RVTEST_IO_WRITE_STR(_SP, _STR)	                                \
    .section .data.string;                                              \
20001:                                                                  \
    .string _STR;                                                       \
    .section .text;                                                     \
    RVTEST_IO_PUSH(_SP)                                                 \
    li x3, 0xF0000000;                                                  \
    la x4, 20001b;                                                      \
2:  lb x5, 0(x4);                                                       \
    sb x5, 0(x3);                                                       \
    beq x5, zero, 1f;                                                   \
    add x4, x4, 1;                                                      \
    j 2b;                                                               \
1:  RVTEST_IO_POP(_SP)

#else // #ifdef _COMPLIANCE_OUTPUT

#define RVTEST_IO_WRITE_STR(_SP, _STR)

#endif // #end #ifdef _COMPLIANCE_OUTPUT

#define RVTEST_IO_INIT
#define RVTEST_IO_CHECK()
#define RVTEST_IO_ASSERT_GPR_EQ(_SP, _R, _I)
#define RVTEST_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVTEST_IO_ASSERT_DFPR_EQ(_D, _R, _I)
#define RVTEST_IO_ASSERT_EQ(_R, _I) 

#endif // _COMPLIANCE_IO_H

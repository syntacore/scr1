/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <crt_tcm.S>
///

#include "riscv_csr_encoding.h"
#include "reloc.h"
#include "sc_test.h"

# define LREG lw
# define SREG sw
# define REGBYTES 4

    .globl _start
    .globl main
    .globl trap_entry
    .globl handle_trap
    .globl sc_exit
    .weak trap_entry, handle_trap

    .section .text.init
    .org (64*3)
    .align 6;
machine_trap_entry:
    j trap_entry

    .align 6
_start:
#ifndef __RVE_EXT
    zero_int_regs 1, 31
#else
    zero_int_regs 1, 15
#endif
    # Global pointer init
    .option push
    .option norelax
    la    gp, __global_pointer$
    .option pop

    RELOC_PROC;

    // init tdata
    mv    a1, tp
    la    a2, _tdata_end
    j     6f
5:  lw    a3, 0(a0)
    sw    a3, 0(a1)
    add   a0, a0, 4
    add   a1, a1, 4
6:  bne   a0, a2, 5b
    // clear tbss
    j     8f
7:  sw    zero, 0(a1)
    add   a1, a1, 4
8:  bne   a1, a4, 7b

    // Timer init
    li    t0, mtime_ctrl
    li    t1, (1 << SCR1_MTIME_CTRL_EN)   // enable, use internal clock
    sw    t1, (t0)
    li    t0, mtime_div
    li    t1, (100-1)                     // divide by 100
    sw    t1, (t0)
    li    t0, mtimecmp
    li    t1, -1
    sw    t1, (t0)                        // max value for mtimecmp
    sw    t1, 4(t0)

    li    a0, 0
    li    a1, 0
    call main
    tail sc_exit

trap_entry:
    addi sp, sp, -272

    SREG x1, 1*REGBYTES(sp)
    SREG x2, 2*REGBYTES(sp)
    SREG x3, 3*REGBYTES(sp)
    SREG x4, 4*REGBYTES(sp)
    SREG x5, 5*REGBYTES(sp)
    SREG x6, 6*REGBYTES(sp)
    SREG x7, 7*REGBYTES(sp)
    SREG x8, 8*REGBYTES(sp)
    SREG x9, 9*REGBYTES(sp)
    SREG x10, 10*REGBYTES(sp)
    SREG x11, 11*REGBYTES(sp)
    SREG x12, 12*REGBYTES(sp)
    SREG x13, 13*REGBYTES(sp)
    SREG x14, 14*REGBYTES(sp)
    SREG x15, 15*REGBYTES(sp)
#ifndef __RVE_EXT
    SREG x16, 16*REGBYTES(sp)
    SREG x17, 17*REGBYTES(sp)
    SREG x18, 18*REGBYTES(sp)
    SREG x19, 19*REGBYTES(sp)
    SREG x20, 20*REGBYTES(sp)
    SREG x21, 21*REGBYTES(sp)
    SREG x22, 22*REGBYTES(sp)
    SREG x23, 23*REGBYTES(sp)
    SREG x24, 24*REGBYTES(sp)
    SREG x25, 25*REGBYTES(sp)
    SREG x26, 26*REGBYTES(sp)
    SREG x27, 27*REGBYTES(sp)
    SREG x28, 28*REGBYTES(sp)
    SREG x29, 29*REGBYTES(sp)
    SREG x30, 30*REGBYTES(sp)
    SREG x31, 31*REGBYTES(sp)
#endif // __RVE_EXT

    csrr a0, mcause
    csrr a1, mepc
    mv a2, sp
    call handle_trap

    LREG x1, 1*REGBYTES(sp)
    LREG x2, 2*REGBYTES(sp)
    LREG x3, 3*REGBYTES(sp)
    LREG x4, 4*REGBYTES(sp)
    LREG x5, 5*REGBYTES(sp)
    LREG x6, 6*REGBYTES(sp)
    LREG x7, 7*REGBYTES(sp)
    LREG x8, 8*REGBYTES(sp)
    LREG x9, 9*REGBYTES(sp)
    LREG x10, 10*REGBYTES(sp)
    LREG x11, 11*REGBYTES(sp)
    LREG x12, 12*REGBYTES(sp)
    LREG x13, 13*REGBYTES(sp)
    LREG x14, 14*REGBYTES(sp)
    LREG x15, 15*REGBYTES(sp)
#ifndef __RVE_EXT
    LREG x16, 16*REGBYTES(sp)
    LREG x17, 17*REGBYTES(sp)
    LREG x18, 18*REGBYTES(sp)
    LREG x19, 19*REGBYTES(sp)
    LREG x20, 20*REGBYTES(sp)
    LREG x21, 21*REGBYTES(sp)
    LREG x22, 22*REGBYTES(sp)
    LREG x23, 23*REGBYTES(sp)
    LREG x24, 24*REGBYTES(sp)
    LREG x25, 25*REGBYTES(sp)
    LREG x26, 26*REGBYTES(sp)
    LREG x27, 27*REGBYTES(sp)
    LREG x28, 28*REGBYTES(sp)
    LREG x29, 29*REGBYTES(sp)
    LREG x30, 30*REGBYTES(sp)
    LREG x31, 31*REGBYTES(sp)
#endif // __RVE_EXT

    addi sp, sp, 272
    mret

handle_trap:
    j SIM_EXIT

// end of crt.S
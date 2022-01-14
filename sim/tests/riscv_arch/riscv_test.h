// See LICENSE for license details.

#ifndef _ENV_PHYSICAL_SINGLE_CORE_H
#define _ENV_PHYSICAL_SINGLE_CORE_H

#include "encoding.h"
#include "sc_test.h"
.noaltmacro

//-----------------------------------------------------------------------
// Begin Macro
//-----------------------------------------------------------------------

#define RVTEST_RV64U                                                    \
  .macro init;                                                          \
  .endm

#define RVTEST_RV64UF                                                   \
  .macro init;                                                          \
  RVTEST_FP_ENABLE;                                                     \
  .endm

#define RVTEST_RV32U                                                    \
  .macro init;                                                          \
  .endm

#define RVTEST_RV32UF                                                   \
  .macro init;                                                          \
  RVTEST_FP_ENABLE;                                                     \
  .endm

#define RVTEST_RV64M                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_MACHINE;                                                \
  .endm

#define RVTEST_RV64S                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_SUPERVISOR;                                             \
  .endm

#define RVTEST_RV32M                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_MACHINE;                                                \
  .endm

#define RVTEST_RV32S                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_SUPERVISOR;                                             \
  .endm

#if __riscv_xlen == 64
# define CHECK_XLEN li a0, 1; slli a0, a0, 31; bgez a0, 1f; RVTEST_PASS; 1:
#else
# define CHECK_XLEN li a0, 1; slli a0, a0, 31; bltz a0, 1f; RVTEST_PASS; 1:
#endif

#define INIT_PMP                                                        \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  li t0, -1;        /* Set up a PMP to permit all accesses */           \
  csrw pmpaddr0, t0;                                                    \
  li t0, PMP_NAPOT | PMP_R | PMP_W | PMP_X;                             \
  csrw pmpcfg0, t0;                                                     \
  .align 2;                                                             \
1:

#define INIT_SATP                                                      \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  csrwi satp, 0;                                                       \
  .align 2;                                                             \
1:

#define DELEGATE_NO_TRAPS                                               \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  csrwi medeleg, 0;                                                     \
  csrwi mideleg, 0;                                                     \
  csrwi mie, 0;                                                         \
  .align 2;                                                             \
1:

#define RVTEST_ENABLE_SUPERVISOR                                        \
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1);                              \
  csrs mstatus, a0;                                                     \
  li a0, SIP_SSIP | SIP_STIP;                                           \
  csrs mideleg, a0;                                                     \

#define RVTEST_ENABLE_MACHINE                                           \
  li a0, MSTATUS_MPP;                                                   \
  csrs mstatus, a0;                                                     \

#define RVTEST_FP_ENABLE                                                \
  li a0, MSTATUS_FS & (MSTATUS_FS >> 1);                                \
  csrs mstatus, a0;                                                     \
  csrwi fcsr, 0

#define RISCV_MULTICORE_DISABLE                                         \
  csrr a0, mhartid;                                                     \
  1: bnez a0, 1b

#define EXTRA_TVEC_USER
#define EXTRA_TVEC_MACHINE
#define EXTRA_INIT
#define EXTRA_INIT_TIMER

#define PRIV_MISA_S  0
//
// undefine some unusable CSR Accesses if no PRIV Mode present
//
#if defined(PRIV_MISA_S)
#  if (PRIV_MISA_S==0)
#    undef  INIT_SATP
#    define INIT_SATP
#    undef  INIT_PMP
#    define INIT_PMP
#    undef  DELEGATE_NO_TRAPS
#    define DELEGATE_NO_TRAPS
#    undef  RVTEST_ENABLE_SUPERVISOR
#    define RVTEST_ENABLE_SUPERVISOR
#  endif
#endif
#if defined(PRIV_MISA_U)
#  if (PRIV_MISA_U==0)
#  endif
#endif
#if defined(TRAPHANDLER)
#include TRAPHANDLER
#endif

#define INTERRUPT_HANDLER j other_exception /* No interrupts should occur */

#define RVTEST_CODE_BEGIN_OLD                                           \
        .section .text.init;                                            \
        .balign  512;                                                   \
        .weak stvec_handler;                                            \
        .weak mtvec_handler;                                            \
        .globl _start;                                                  \
_start:                                                                 \
        /* reset vector */                                              \
        j reset_vector;                                                 \
        .balign 64;                                                     \
trap_vector:                                                            \
        /* test whether the test came from pass/fail */                 \
        csrr a4, mcause;                                                \
        li a5, CAUSE_USER_ECALL;                                        \
        beq a4, a5, write_tohost;                                       \
        li a5, CAUSE_SUPERVISOR_ECALL;                                  \
        beq a4, a5, write_tohost;                                       \
        li a5, CAUSE_MACHINE_ECALL;                                     \
        beq a4, a5, write_tohost;                                       \
        /* if an mtvec_handler is defined, jump to it */                \
        la a4, mtvec_handler;                                           \
        beqz a4, 1f;                                                    \
        jr a4;                                                          \
        /* was it an interrupt or an exception? */                      \
1:      csrr a4, mcause;                                                \
        bgez a4, handle_exception;                                      \
        INTERRUPT_HANDLER;                                              \
handle_exception:                                                       \
        /* we don't know how to handle whatever the exception was */    \
  other_exception:                                                      \
        /* some unhandlable exception occurred */                       \
  1:    ori TESTNUM, TESTNUM, 1337;                                     \
  write_tohost:                                                         \
        tail sc_exit;                                                   \
reset_vector:                                                           \
        RISCV_MULTICORE_DISABLE;                                        \
        INIT_SATP;                                                     \
        INIT_PMP;                                                       \
        DELEGATE_NO_TRAPS;                                              \
        li TESTNUM, 0;                                                  \
        la t0, trap_vector;                                             \
        csrw mtvec, t0;                                                 \
        CHECK_XLEN;                                                     \
        /* if an stvec_handler is defined, delegate exceptions to it */ \
        la t0, stvec_handler;                                           \
        beqz t0, 1f;                                                    \
        csrw stvec, t0;                                                 \
        li t0, (1 << CAUSE_LOAD_PAGE_FAULT) |                           \
               (1 << CAUSE_STORE_PAGE_FAULT) |                          \
               (1 << CAUSE_FETCH_PAGE_FAULT) |                          \
               (1 << CAUSE_MISALIGNED_FETCH) |                          \
               (1 << CAUSE_USER_ECALL) |                                \
               (1 << CAUSE_BREAKPOINT);                                 \
        csrw medeleg, t0;                                               \
        csrr t1, medeleg;                                               \
        bne t0, t1, other_exception;                                    \
1:      csrwi mstatus, 0;                                               \
        init;                                                           \
        EXTRA_INIT;                                                     \
        EXTRA_INIT_TIMER;                                               \
        la t0, 1f;                                                      \
        csrw mepc, t0;                                                  \
        csrr a0, mhartid;                                               \
        mret;                                                           \
1:                                                                      \
begin_testcode:


//-----------------------------------------------------------------------
// End Macro
//-----------------------------------------------------------------------

#define RVTEST_CODE_END_OLD                                             \
end_testcode:                                                           \
        ecall;

//-----------------------------------------------------------------------
// Pass/Fail Macro
//-----------------------------------------------------------------------
#define RVTEST_SYNC fence
//#define RVTEST_SYNC nop

#define RVTEST_PASS                                                     \
        RVTEST_SYNC;                                                    \
        li TESTNUM, 1;                                                  \
        SWSIG (0, TESTNUM);                                             \
        ecall

#define TESTNUM gp
#define RVTEST_FAIL                                                     \
        RVTEST_SYNC;                                                    \
1:      beqz TESTNUM, 1b;                                               \
        sll TESTNUM, TESTNUM, 1;                                        \
        or TESTNUM, TESTNUM, 1;                                         \
        SWSIG (0, TESTNUM);                                             \
        la x1, end_testcode;                                            \
        jr x1;

//-----------------------------------------------------------------------
// Data Section Macro
//-----------------------------------------------------------------------

#define EXTRA_DATA

#define RVTEST_DATA_BEGIN_OLD                                               \
        .align 4; .global begin_signature; begin_signature:

#define RVTEST_DATA_END_OLD                                                 \
        .balign 4; .global end_signature; end_signature:                 \
        EXTRA_DATA                                                      \
        .pushsection .tohost,"aw",@progbits;                            \
        .align 8; .global tohost; tohost: .dword 0;                     \
        .align 8; .global fromhost; fromhost: .dword 0;                 \
        .popsection;                                                    \
        .align 8; .global begin_regstate; begin_regstate:               \
        .word 128;                                                      \
        .align 8; .global end_regstate; end_regstate:                   \
        .word 4;

#endif

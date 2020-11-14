#include "riscv_macros.h"
#include "sc_test.h"

.altmacro
// global interrupt bit
#define MSIE                        (1 << IRQ_M_SOFT)       //machine software interrupt enable
#define MTIE                        (1 << IRQ_M_TIMER)      //machine timer interrupt enable
#define MEIE                        (1 << IRQ_M_EXT)        //machine external interrupt enable
#define MCAUSE_EXT_IRQ              (1 << 31 | IRQ_M_EXT)
#define MCAUSE_SOFT_IRQ             (1 << 31 | IRQ_M_SOFT)
#define MCAUSE_TMR_IRQ              (1 << 31 | IRQ_M_TIMER)

// IPIC
#define IRQ_LINES_ADDR              0xF0000100      // simulation
#define TRIG_EXT_IRQ_ADDR           0xF0000100      // external irq is triggered when tb memory is set to non-zero
#define TRIG_SW_IRQ_ADDR            0xF0000200      // software irq is triggered when tb memory is set to non-zero

#define IPIC_EOI                    0xBF4           // end of interrupt
#define IPIC_SOI                    0xBF5           // start of interrupt
#define IPIC_IDX                    0xBF6           // index register
#define IPIC_ICSR                   0xBF7           // interrupt control status register

// IPIC Interrupt Constrol Status Register
#define IPIC_ICSR_IP                (1 << 0)        // interrupt pending
#define IPIC_ICSR_IE                (1 << 1)        // interrupt enable
#define IPIC_ICSR_IM                (1 << 2)        // interrupt mode (0/1: level/edge)
#define IPIC_ICSR_INV               (1 << 3)        // line inversion
#define IPIC_ICSR_IS                (1 << 4)        // in service

//  Interrupt lines in use 
#define IPIC_IRQ_LINE9              9
#define EXT_IRQ_LINE_COMMON         0

#include "timer.h"
#include "reloc.h"

.macro jmp_sc_exit
    la  t0, sc_exit
    jr  t0
.endm

    .section .text.init
    .option norvc
    .globl _start
//  -----------------------------------------------------------------
// Trap handlers
// 0xXXXXXX00
    .option norvc
.org (64*3)

//0xXXXXXXC0
    .balign 64
machine_trap_entry:
vec_usr_soft:
#ifdef VECT_IRQ_ENABLED
    trap_entry:
        j    _trap_fail
    vec_supervisor_soft:
        j    _trap_fail
    vec_reserved1:
        j    _trap_fail
    vec_machine_soft:
        j    vec_machine_soft_handler
    vec_usr_tmr:
        j    _trap_fail
    vec_supervisor_tmr:
        j    _trap_fail
    vec_reserved2:
        j    _trap_fail
    vec_machine_tmr:
        j    vec_machine_tmr_handler
    vec_usr_ext:
        j    _trap_fail
    vec_supervisor_ext:
        j    _trap_fail
    vec_reserved3:
        j    _trap_fail
    vec_machine_ext:
        j    vec_machine_ext_handler
    vec_reserved4:
        j    _trap_fail
        j    _trap_fail
        j    _trap_fail
        j    _trap_fail
#else
    trap_entry:
        j    direct_irq_handler
    vec_supervisor_soft:
        j    _trap_fail
    vec_reserved1:
        j    _trap_fail
    vec_machine_soft:
        j    _trap_fail
    vec_usr_tmr:
        j    _trap_fail
    vec_supervisor_tmr:
        j    _trap_fail
    vec_reserved2:
        j    _trap_fail
    vec_machine_tmr:
        j    _trap_fail
    vec_usr_ext:
        j    _trap_fail
    vec_supervisor_ext:
        j    _trap_fail
    vec_reserved3:
        j    _trap_fail
    vec_machine_ext:
        j    _trap_fail
    vec_reserved4:
        j    _trap_fail
        j    _trap_fail
        j    _trap_fail
        j    _trap_fail

#endif // ifdef VECT_IRQ_ENABLED


    .balign 64
_start:
    la                  t0, machine_trap_entry
    csrw                mtvec, t0

    la                  t0,  test_start
    jr                  (t0)

//  -----------------------------------------------------------------
    .option norvc
    .balign 64
test_start:
    
    la                  t0, trap_entry
    csrw                mtvec, t0                          // set mtvec to trap_entry
    #ifdef VECT_IRQ_ENABLED
        csrsi               mtvec, 1                       // set vectored mode
    #else
        csrsi               mtvec, 0                       // set direct mode
    #endif

    /// configuring timer interrupt /// 
    _reset_mtimecmp;                                   // reset timer
    _run_timer;                                        // run timer
    csrs                mstatus, MSTATUS_MIE           // enable global interrupt
    li                  a0, MTIE                       
    csrs                mie, a0                        // enable timer interrupt
    li                  t2, 0                          // reset timer counter = 0 (updated in isr)
    _read_mtime         s1                             // read timer value
    addi                s1, s1, 256
    _write_mtimecmp_32  s1 
    wfi  


   /// configuring external interrupt /// 
    csrw                mie, zero                      // disable all interrupts
    li                  t0, IRQ_LINES_ADDR
    sh                  zero, (t0)                     // set all exterinal interrupt lines low
    #ifdef IPIC_ENABLED
        li                  t0, IPIC_IRQ_LINE9
        csrw                IPIC_IDX, t0               // set IPIC to expect interupt on line 9...
        li                  t0, (IPIC_ICSR_IE | IPIC_ICSR_IM)
        csrw                IPIC_ICSR, t0              //  ....enable interrupt,set edge interrupt mode
    #endif
    li                  t0, MEIE
    csrs                mie, t0                        // enable external interrupt 
    li                  t0, TRIG_EXT_IRQ_ADDR
    #ifdef IPIC_ENABLED          
        li                  t1, (1 << IPIC_IRQ_LINE9)
    #else
        li                  t1, (1 << EXT_IRQ_LINE_COMMON)
    #endif
    sh                  t1, (t0)                       //send command to generate external interrupt on line 9 to testbench
    nop
    nop
    nop
    nop                                                //wait for external interrupt


    /// configuring software interrupt /// 
    csrw                mie, zero                      // disable all interrupts
    li                  t0, TRIG_SW_IRQ_ADDR
    li                  t1, 0x00000001
    sh                  t1, (t0)                       //send command to generate software interrupt 
    li                  t0, MSIE
    csrs                mie, t0                        // enable software interrupt 
    nop
    nop
    nop
    nop                                                //wait for software interrupt

    li                  s1, 3
    li                  a0, 0
    beq                 t2, s1, 1f
    li                  a0, -1
1:
    jmp_sc_exit


#ifndef VECT_IRQ_ENABLED

direct_irq_handler:
    csrr            a1, mcause
    li              a5, MCAUSE_TMR_IRQ      //0x80000007 -- mcause = tmr.irq
    beq             a1, a5, vec_machine_tmr_handler
    li              a5, MCAUSE_SOFT_IRQ     //0x80000003 -- mcause = soft.irq
    beq             a1, a5, vec_machine_soft_handler
    li              a5, MCAUSE_EXT_IRQ      //0x8000000B -- mcause = ext.irq
    beq             a1, a5, vec_machine_ext_handler
    mret
#endif

vec_machine_tmr_handler:
    csrr            a1, mcause
    li              a5, MCAUSE_TMR_IRQ      //0x80000007 -- mcause = tmr.irq
    li              a0, -1
    bne             a1, a5, check_fail
    csrr            t1, mip
    li              t0, MIP_MTIP
    and             t0, t1, t0
    beqz            t0, check_fail
#ifdef IPIC_ENABLED
    csrw            IPIC_SOI, zero
    csrw            IPIC_EOI, zero
#endif
    _reset_mtimecmp
    csrr            t1, mip
    andi            t1, t1, MIP_MTIP
    bne             t1, zero, check_fail
    addi            t2, t2, 1               // tmr irq counter update
    mret

vec_machine_ext_handler:

    csrr            a1, mcause
    li              a5, MCAUSE_EXT_IRQ      //0x8000000B -- mcause = ext.irq
    li              a0, -1
    bne             a1, a5, check_fail
    csrr            t1, mip
    li              t0, MIP_MEIP
    and             t0, t1, t0
    beqz            t0, check_fail
#ifdef IPIC_ENABLED
    csrw            IPIC_SOI, zero
    csrw            IPIC_EOI, zero
#endif
    li                  t0, MEIE
    csrc                mie, t0             // disable software interrupt 

    li              t0, TRIG_EXT_IRQ_ADDR
    li              t1, EXT_IRQ_LINE_COMMON         
    sh              t1, (t0)                // send command to disable external interrupt 
     
    csrr            t1, mip
    li              t0, MIP_MEIP
    bne             t1, zero, check_fail
    addi            t2, t2, 1               // ext irq counter update
    mret

vec_machine_soft_handler:
    csrr            a1, mcause
    li              a5, MCAUSE_SOFT_IRQ     //0x80000003 -- mcause = soft.irq
    li              a0, -1
    bne             a1, a5, check_fail
    csrr            t1, mip
    li              t0, MIP_MSIP
    and             t0, t1, t0
    beqz            t0, check_fail
    #ifdef IPIC_ENABLED
       csrw         IPIC_SOI, zero
       csrw         IPIC_EOI, zero
    #endif
    li              t0, MSIE
    csrc            mie, t0                 // disable software interrupt 
    li              t0, TRIG_SW_IRQ_ADDR
    li              t1, 0x00000000
    sh              t1, (t0)                // send command to stop generating  software interrupt 
    li              t0, MIP_MSIP
    csrc            mip, t0
    csrr            t1, mip
    li              t0, MIP_MSIP
    and             t1, t1, t0
    bne             t1, zero, check_fail
    addi            t2, t2, 1               // ext irq counter update
    mret

check_fail:
    la              t0, sc_exit
    jr              t0

_trap_fail:
    li              a0, -1
    j               check_fail

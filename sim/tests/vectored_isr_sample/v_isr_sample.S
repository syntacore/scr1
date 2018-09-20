#include "riscv_macros.h"
#include "sc_test.h"

.altmacro
// global interrupt bit
#define MTIE                        (1 << IRQ_M_TIMER)
#define MEIE                        (1 << IRQ_M_EXT)
#define MCAUSE_EXT_IRQ              (1 << 31 | IRQ_M_EXT)

// IPIC
#define IRQ_LINES_ADDR              0xF0000100      // simulation
#define IPIC_EOI                    0xBF4
#define IPIC_SOI                    0xBF5
#define IPIC_IDX                    0xBF6
#define IPIC_ICSR                   0xBF7
#define IPIC_ICSR_IP                (1 << 0)
#define IPIC_ICSR_IE                (1 << 1)
#define IPIC_ICSR_IM                (1 << 2)
#define IPIC_ICSR_INV               (1 << 3)
#define IPIC_ICSR_IS                (1 << 4)

#include "timer.h"

.macro jmp_sc_exit
    la  t0, sc_exit
    jr  t0
.endm

//  -----------------------------------------------------------------
// Trap handlers
// 0x100
    .text
    .option norvc
    .align 6
user_trap_entry:
    csrr  a5, instret
    csrr  a1, mcause
    csrr  a2, mepc
    csrr  a3, mbadaddr
    csrr  a4, mstatus
    li    a0, 0x100
    jmp_sc_exit

//0x140
    .align 6
supervisor_trap_entry:
    csrr  a5, instret
    csrr  a1, mcause
    csrr  a2, mepc
    csrr  a3, mbadaddr
    csrr  a4, mstatus
    li    a0, 0x140
    jmp_sc_exit

//0x180
    .align 6
hypervisor_trap_entry:
    csrr  a5, instret
    csrr  a1, mcause
    csrr  a2, mbadaddr
    csrr  a3, mepc
    csrr  a4, mstatus
    li    a0, 0x180
    jmp_sc_exit

//0x1C0
    .align 6
vec_usr_soft:
// machine_trap_entry:
trap_entry:
    j    _trap_fail
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

//0x200
    .globl _start
_start:
    // vectored mode
    csrsi               mtvec, 1
    _reset_mtimecmp;
    _run_timer;
    // then enable global interrrupt
    csrs                mstatus, MSTATUS_MIE
    // enable tmr irq
    li                  a0, MTIE
    csrs                mie, a0
    // timer counter = 0 (updated in isr)
    li                  t2, 0
    _read_mtime         s1
    addi                s1, s1, 256
    _write_mtimecmp_32  s1
    wfi
    // disable all irq
    csrw                mie, zero
    // setup IPIC
    li                  t0, IRQ_LINES_ADDR
    sh                  zero, (t0)
    li                  t0, 9           // IPIC irq 9
    csrw                IPIC_IDX, t0
    li                  t0, (IPIC_ICSR_IE | IPIC_ICSR_IM)
    csrw                IPIC_ICSR, t0   // enable, rising edge
    li                  t0, MEIE
    csrs                mie, t0
    li                  t0, IRQ_LINES_ADDR
    li                  t1, (1 << 9)
    sh                  t1, (t0)
    wfi
    li                  s1, 2
    li                  a0, 0
    beq                 t2, s1, 1f
    li                  a0, -1
1:
    jmp_sc_exit


vec_machine_tmr_handler:
    csrr            a1, mcause
    li              a5, MCAUSE_TMR_IRQ     //0x80000007 -- mcause = tmr.irq
    li              a0, -1
    bne             a1, a5, check_fail
    csrr            t1, mip
    li              t0, MIP_MTIP
    and             t0, t1, t0
    beqz            t1, check_fail
    _reset_mtimecmp
    csrr            t1, mip
    andi            t1, t1, MIP_MTIP
    bne             t1, zero, check_fail
    addi            t2, t2, 1              // tmr irq counter update
    mret

vec_machine_ext_handler:
    csrr            a1, mcause
    li              a5, MCAUSE_EXT_IRQ     //0x8000000B -- mcause = ext.irq
    li              a0, -1
    bne             a1, a5, check_fail
    csrr            t1, mip
    li              t0, MIP_MEIP
    and             t0, t1, t0
    beqz            t1, check_fail
    csrw            IPIC_SOI, zero
    csrw            IPIC_EOI, zero
    csrr            t1, mip
    li              t0, MIP_MEIP
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

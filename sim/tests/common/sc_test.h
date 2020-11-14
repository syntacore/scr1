/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <sc_test.h>
///

#ifndef SC_TEST_H
#define SC_TEST_H

#if defined(__ASSEMBLER__)
.altmacro

.macro zero_int_reg regn
mv   x\regn, zero
.endm

.macro zero_int_regs reg_first, reg_last
.set regn, \reg_first
.rept \reg_last - \reg_first + 1
zero_int_reg %(regn)
.set regn, regn+1
.endr
.endm

#define report_results(result) \
li  a0, result;  \
la t0, sc_exit;  \
jr	 t0;

.pushsection sc_test_section, "ax"
sc_exit: la t0, SIM_EXIT; jr t0;
.balign 32
.popsection
#define sc_pass report_results(0x0)
#define sc_fail report_results(0x1)

#else

extern void sc_exit(unsigned result, unsigned res0, unsigned res1, unsigned res2, unsigned res3)
    __attribute__ ((noinline, noreturn));

static inline void  __attribute__ ((noreturn))
report_results(unsigned result, unsigned res0, unsigned res1, unsigned res2, unsigned res3)
{
    sc_exit(result, res0, res1, res2, res3);
}

#endif

#endif // SC_TEST_H

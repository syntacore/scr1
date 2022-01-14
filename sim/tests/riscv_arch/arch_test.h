#include "encoding.h"
#include "sc_test.h"
// TODO the following should come from the YAML.
#ifndef NUM_SPECD_INTCAUSES
  #define NUM_SPECD_INTCAUSES 16
#endif
//#define RVTEST_FIXED_LEN
#ifndef UNROLLSZ
  #define UNROLLSZ 5
#endif
// #ifndef rvtest_gpr_save
//   #define rvtest_gpr_save
// #endif

#define TEST_CASE_1

//-----------------------------------------------------------------------
// RV Arch Test Macros
//-----------------------------------------------------------------------
#ifndef RVMODEL_SET_MSW_INT
  #warning "RVMODEL_SET_MSW_INT is not defined by target. Declaring as empty macro"
  #define RVMODEL_SET_MSW_INT
#endif

#ifndef RVMODEL_CLEAR_MSW_INT
  #warning "RVMODEL_CLEAR_MSW_INT is not defined by target. Declaring as empty macro"
  #define RVMODEL_CLEAR_MSW_INT
#endif

#ifndef RVMODEL_CLEAR_MTIMER_INT
  #warning "RVMODEL_CLEAR_MTIMER_INT is not defined by target. Declaring as empty macro"
  #define RVMODEL_CLEAR_MTIMER_INT
#endif

#ifndef RVMODEL_CLEAR_MEXT_INT
  #warning "RVMODEL_CLEAR_MEXT_INT is not defined by target. Declaring as empty macro"
  #define RVMODEL_CLEAR_MEXT_INT
#endif

#ifdef RVTEST_FIXED_LEN
    #define LI(reg, val)\
    .option push;\
    .option norvc;\
    .align UNROLLSZ;\
        li reg,val;\
    .align UNROLLSZ;\
    .option pop;

    #define LA(reg, val)\
    .option push;\
    .option norvc;\
    .align UNROLLSZ;\
        la reg,val;\
    .align UNROLLSZ;\
    .option pop;

#else
    #define LI(reg,val);\
        .option push;\
        .option norvc;\
        li reg,val;\
        .option pop;

    #define LA(reg,val);\
        .option push;\
        .option norvc;\
        la reg,val;\
        .option pop;
#endif
#if XLEN==64
  #define SREG sd
  #define LREG ld
  #define REGWIDTH 8
  #define MASK 0xFFFFFFFFFFFFFFFF

#else
  #if XLEN==32
    #define SREG sw
    #define LREG lw
    #define REGWIDTH 4
  #define MASK 0xFFFFFFFF

  #endif
#endif
#define MMODE_SIG 3
#define RLENG (REGWIDTH<<3)

#define RVTEST_ISA(_STR)

#ifndef DATA_REL_TVAL_MSK
  #define DATA_REL_TVAL_MSK 0x0F05 << (REGWIDTH*8-16)
#endif

#ifndef CODE_REL_TVAL_MSK
  #define CODE_REL_TVAL_MSK 0xD008 << (REGWIDTH*8-16)
#endif


// ----------------------------------- CODE BEGIN w/ TRAP HANDLER START ------------------------ //

.macro RVTEST_CODE_BEGIN
  .align UNROLLSZ
  .section .text.init;
  .globl rvtest_init;                                                  \
  rvtest_init:
#ifdef rvtest_mtrap_routine
  LA(x1, rvtest_trap_prolog );
  jalr ra, x1
  rvtest_prolog_done:
#endif
     LI (x1,  (0xFEEDBEADFEEDBEAD & MASK));
     LI (x2,  (0xFF76DF56FF76DF56 & MASK));
     LI (x3,  (0x7FBB6FAB7FBB6FAB & MASK));
     LI (x4,  (0xBFDDB7D5BFDDB7D5 & MASK));
     LA (x5, rvtest_code_begin);
     LA (x6, rvtest_data_begin);
     LI (x7,  (0xB7FBB6FAB7FBB6FA & MASK));
     LI (x8,  (0x5BFDDB7D5BFDDB7D & MASK));
     LI (x9,  (0xADFEEDBEADFEEDBE & MASK));
     LI (x10, (0x56FF76DF56FF76DF & MASK));
     LI (x11, (0xAB7FBB6FAB7FBB6F & MASK));
     LI (x12, (0xD5BFDDB7D5BFDDB7 & MASK));
     LI (x13, (0xEADFEEDBEADFEEDB & MASK));
     LI (x14, (0xF56FF76DF56FF76D & MASK));
     LI (x15, (0xFAB7FBB6FAB7FBB6 & MASK));
     #ifndef RVTEST_E
     LI (x16, (0x7D5BFDDB7D5BFDDB & MASK));
     LI (x17, (0xBEADFEEDBEADFEED & MASK));
     LI (x18, (0xDF56FF76DF56FF76 & MASK));
     LI (x19, (0x6FAB7FBB6FAB7FBB & MASK));
     LI (x20, (0xB7D5BFDDB7D5BFDD & MASK));
     LI (x21, (0xDBEADFEEDBEADFEE & MASK));
     LI (x22, (0x6DF56FF76DF56FF7 & MASK));
     LI (x23, (0xB6FAB7FBB6FAB7FB & MASK));
     LI (x24, (0xDB7D5BFDDB7D5BFD & MASK));
     LI (x25, (0xEDBEADFEEDBEADFE & MASK));
     LI (x26, (0x76DF56FF76DF56FF & MASK));
     LI (x27, (0xBB6FAB7FBB6FAB7F & MASK));
     LI (x28, (0xDDB7D5BFDDB7D5BF & MASK));
     LI (x29, (0xEEDBEADFEEDBEADF & MASK));
     LI (x30, (0xF76DF56FF76DF56F & MASK));
     LI (x31, (0xFBB6FAB7FBB6FAB7 & MASK));
     #endif
  .globl rvtest_code_begin
  rvtest_code_begin:
.endm

// --------------------------------- CODE BEGIN w/ TRAP HANDLER END -----------------------------//

.macro RVTEST_CODE_END
  .align 4;
  .global rvtest_code_end
  rvtest_code_end:
#ifdef rvtest_mtrap_routine
  .option push
  .option norvc
  j exit_cleanup

  rvtest_trap_prolog:
  /******************************************************************************/
  /****                 Prolog, to be run before any tests                   ****/
  /****       #include 1 copy of this per mode in rvmodel_boot code?         ****/
  /**** -------------------------------------------------------------------  ****/
  /**** if xTVEC isn't completely RW, then we need to change the code at its ****/
  /**** target. The entire trap trampoline and mtrap handler replaces the    ****/
  /**** area pointed to by mtvec, after saving its original contents first.  ****/
  /**** If it isn't possible to fully write that area, restore and fail.     ****/
  /******************************************************************************/

  //trap_handler_prolog; enter with t1..t6 available

  init_mscratch:
  	la	t1, trapreg_sv
  	csrrw	t1, CSR_MSCRATCH, t1	// swap old mscratch. mscratch not points to trapreg_sv
  	la	t2, mscratch_save
  	SREG	t1, 0(t2)		        // save old mscratch in mscratch_save region
    csrr t1, CSR_MSCRATCH       // read the trapreg_sv address
    LA( t2, mtrap_sigptr   ) // locate the start of the trap signature
    SREG  t2, 0(t1)           // save mtrap_sigptr at first location of trapreg_sv
  init_mtvec:
  	la	t1, mtrampoline
  	la	t4, mtvec_save
  	csrrw	t2, CSR_MTVEC, t1		          // swap mtvec and trap_trampoline
  	SREG	t2, 0(t4)		              // save orig mtvec
  	csrr	t3, CSR_MTVEC		              // now read new_mtval back
  	beq	t3, t1, rvtest_prolog_done // if mtvec==trap_trampoline, mtvec is writable, continue

  /****************************************************************/
  /**** fixed mtvec, can't move it so move trampoline instead  ****/
  /**** t1=trampoline, t2=oldmtvec, t3=save area, t4=save end  ****/
  /****************************************************************/

  // t2 = dut's original mtvec setting
  // t1 = mtrampoline address
  init_tramp:	/**** copy trampoline at mtvec tgt ****/

  	csrw	CSR_MTVEC, t2		// restore orig mtvec, will now attemp to copy trampoline to it
  	la	t3, tramptbl_sv		// addr of save area
  	addi	t4, t3, NUM_SPECD_INTCAUSES*4 // end of save area

  overwrite_tt:			            // now build new trampoline table with offsets base from curr mtvec
  	lw	t6, 0(t2)		            // get original mtvec target
  	sw	t6, 0(t3)		            // save it
  	lw	t5, 0(t1)		            // get trampoline src
  	sw	t5, 0(t2)		            // overwrite mtvec target
  	lw	t6, 0(t2)		            // rd it back to make sure it was written
  	bne	t6, t5, resto_tramp		  // table isn't fully writable, restore and give up
  	addi	t1, t1, 4		          // next src  index
  	addi	t2, t2, 4		          // next tgt  index
  	addi	t3, t3, 4		          // next save index
  	bne	t3, t4, overwrite_tt		// not done,  loop
  	j rvtest_prolog_done

  resto_tramp:			                      // vector table not writeable, restore
  	LREG	t1, 16(t4)            // load mscratch_SAVE at fixed offset from table end
  	csrw	CSR_MSCRATCH, t1		                // restore mscratch
  	LREG	t4, 8(t4)             // load mtvec_SAVE (used as end of loop marker)


  resto_loop:	              // goes backwards, t2= dest vec tbl ptr, t3=src save area ptr, t4=vec tbl begin
  	lw	t6, 0(t3)		        // read saved tgt entry
  	sw	t6, 0(t2)		        // restore original tgt
  	addi	t2, t2, -4		    // prev tgt  index
  	addi	t3, t3, -4		    // prev save index
  	bne	t2, t4, resto_loop  // didn't restore to begining yet,  loop

  	j	rvtest_end // failure to replace trampoline


  #define mhandler			\
    csrrw   sp, CSR_MSCRATCH, sp;	\
    SREG      t6, 6*REGWIDTH(sp);	\
    jal t6, common_prolog;

  /**********************************************************************/
  /**** This is the entry point for all m-modetraps, vectored or not.****/
  /**** At entry, mscratch will contain a pointer to a scratch area. ****/
  /**** This is an array of branches at 4B intevals that spreads out ****/
  /**** to an array of 32B mhandler macros for specd int causes, and ****/
  /**** to a return for anything above that (which causes a mismatch)****/
  /**********************************************************************/
  .balign 64
  mtrampoline:		// 64 or 32 entry table
  value = 0
  .rept NUM_SPECD_INTCAUSES     	  // located at each possible int vectors
     j	mtrap_handler + 12*(value)  //offset < +/- 1MB
     value = value + 1
  .endr
  .rept RLENG-NUM_SPECD_INTCAUSES   // fill at each impossible entry
  	mret
  .endr

  mtrap_handler:		/* after executing, sp points to temp save area, t4 is PC */
  .rept NUM_SPECD_INTCAUSES
    mhandler
  .endr

  common_prolog:
    la t5, common_mhandler
    jr t5
  /*********************************************************************/
  /**** common code for all ints & exceptions, will fork to handle  ****/
  /**** each separately. The common handler first stores trap mode+ ****/
  /**** vector, and mcause signatures. All traps have 4wd sigs, but ****/
  /**** sw and timer ints only store 3 of the 4.                    ****/
  /**** sig offset Exception    ExtInt       SWInt        TimerInt  ****/
  /****         0: tval         IntID        -1           -1        ****/
  /****         4: mepc         mip          mip          mip       ****/
  /****         8: <----------------------  mcause ------------->   ****/
  /****        12: <---------------------  Vect+mode  ---------->   ****/
  /*********************************************************************/
  /*   in general, CSRs loaded in t2, addresses into t3                */

  common_mhandler:                 /* enter with link in t6 */
          SREG      t5, 5*REGWIDTH(sp)
          SREG      t4, 4*REGWIDTH(sp)
          SREG      t3, 3*REGWIDTH(sp)
          SREG      t2, 2*REGWIDTH(sp)
          SREG      t1, 1*REGWIDTH(sp)  /* save other temporaries */

          LREG      t1, 0(sp)        /* load trap sig pointer (runs backwards from DATA_END) */

          LA(     t3, mtrampoline)
          sub     t2, t6, t3       /* reloc “link” to 0..63 to show which int vector was taken */
          addi    t2, t2, MMODE_SIG   /* insert mode# into 1:0  */
          SREG      t2, 0*REGWIDTH(t1)        /* save 1st sig value, (vect, trapmode) */
  sv_mcause:
          csrr   t2, CSR_MCAUSE
          SREG      t2, 1*REGWIDTH(t1) /* save 2nd sig value, (mcause)  */

          bltz    t2, common_mint_handler /* this is a interrupt, not a trap */

  /********************************************************************/
  /**** This is the exceptions specific code, storing relative mepc****/
  /**** & relative tval signatures. tval is relocated by code or   ****/
  /**** data start, or 0 depending on mcause. mepc signature value ****/
  /**** is relocated by code start, and restored adjusted depending****/
  /**** on op alignment so trapped op isn't re-executed.           ****/
  /********************************************************************/
  common_mexcpt_handler:
          csrr   t2, CSR_MEPC
  sv_mepc:
          LA(     t3, rvtest_prolog_done) /* offset to compensate for different loader offsets */
          sub     t4, t2, t3      /* convert mepc to rel offset of beginning of test*/
          SREG      t4, 2*REGWIDTH(t1) /* save 3rd sig value, (rel mepc) into trap signature area */
  adj_mepc:   		//adj mepc so there is padding after op, and its 8B aligned
        andi    t4, t2, 0x2     /* set to 2 if mepc was misaligned */
        sub     t2, t2, t4      /* adjust mepc to prev 4B alignment */
        addi    t2, t2, 0x8     /* adjust mepc, so it skips past the op, has padding & is 4B aligned */
        csrw    CSR_MEPC, t2	/* restore adjusted value, has 1,2, or 3 bytes of padding */


  /* calculate relative mtval if it’s an address  (by code_begin or data_begin amt)  */
  /* note that masks that determine this are implementation specific from YAML */

  /* masks are bit reversed, so mcause==0 bit is in MSB (so different for RV32 and RV64) */

  adj_mtval:
        	csrr   t2, CSR_MCAUSE  /* code begin adjustment amount already in t3 */

          LI(t4, CODE_REL_TVAL_MSK)   /* trap#s 12, 3,1,0, -- adjust w/ code_begin */
          sll     t4, t4, t2		          /* put bit# in MSB */
          bltz    t4, sv_mtval		        /* correct adjustment is code_begin in t3 */

          LA(     t3, mtrap_sigptr) /* adjustment assuming access is to signature region */
          LI(t4, DATA_REL_TVAL_MSK)       /* trap#s not 14, 11..8, 2 adjust w/ data_begin */
          sll     t4, t4, t2		          /* put bit# in MSB */
          bgez    t4, no_adj		          /* correct adjustment is data_begin in t3 */
  sigbound_chk:
          csrr t4, CSR_MTVAL                  /* do a bounds check on mtval */
          bge   t3, t4, sv_mtval          /* if mtval is greater than the rvmodel_data_begin then use that as anchor */
          LA( t3, rvtest_data_begin)      /* else change anchor to rvtest_data_begin  */
          blt   t3, t4, sv_mtval          /* before the signature, use data_begin adj */
          mv t4, t3                       /* use sig relative adjust */
  no_adj:
          LI(t3, 0)			/* else zero adjustment amt */

  // For Illegal op handling
          addi    t2, t2, -2            /* check if mcause==2 (illegal op) */
          bnez    t2, sv_mtval          /* not illegal op, no special treatment */
          csrr    t2, CSR_MTVAL
          bnez    t2, sv_mtval          /* mtval isn’t zero, no special treatment */
  illop:
          LI(t5, 0x20000)           /* get mprv mask */
          csrrs   t5, CSR_MSTATUS, t5       /* set mprv while saving the old value */
          csrr    t3, CSR_MEPC
          lhu     t2, 0(t3)             /* load 1st 16b of opc w/ old priv, endianess*/
          andi    t4, t2,  0x3
          addi    t4, t4, -0x3          /* does opcode[1:0]==0b11? (Meaning >16b op) */
          bnez    t4, sv_mtval          /* entire mtval is in tt2, adj amt will be set to zero */
          lhu     t4, 2(t3)
          sll     t4, t4, 16
          or      t3, t2, t4            /* get 2nd  hwd, align it & insert it into opcode */
          csrw    CSR_MSTATUS, t5           /* restore mstatus */

/*******FIXME: this will not handle 48 or 64b opcodes in an RV64) ********/

  sv_mtval:
          csrr   t2, CSR_MTVAL
          sub    t2, t2, t3		/* perform mtval adjust by either code or data position or zero*/
          SREG   t2, 3*REGWIDTH(t1)	/* save 4th sig value, (rel mtval) into trap signature area */

  resto_rtn:		/* restore and return */
          addi    t1, t1,4*REGWIDTH		/* adjust trap signature ptr (traps always save 4 words) */
          SREG      t1, 0*REGWIDTH(sp) 	/* save updated trap sig pointer (pts to trap_sigptr */

          LREG      t1, 1*REGWIDTH(sp)
          LREG      t2, 2*REGWIDTH(sp)
          LREG      t3, 3*REGWIDTH(sp)
          LREG      t4, 4*REGWIDTH(sp)
          LREG      t5, 5*REGWIDTH(sp)
          LREG      t6, 6*REGWIDTH(sp)  /* restore temporaries */

          csrrw   sp, CSR_MSCRATCH, sp /* restore sp from scratch */
          mret

  common_mint_handler:    /* t1 has sig ptr, t2 has mcause */

          LI(t3, 1)
          sll     t3, t3, t2      /* create mask 1<<mcause */
          csrrc   t4, CSR_MIP, t3     /* read, then attempt to clear int pend bit */
          csrrc   t4, CSR_MIE, t3     /* read, then attempt to clear int pend bit */
  sv_mip:	/* note: clear has no effect on MxIP */
          SREG      t4, 2*REGWIDTH(t1) /* save 3rd sig value, (mip)  */

  /* case table branch to interrupt clearing code, depending on mcause */
  	slli	t2, t2, 3       /* convert mcause to 8B offset */
  	LA(	t3, clrint_tbl ) /* load jump table address */
  	add	t3, t3, t2      /* index into to it, load vector, then jump to it */
  	LREG	t3, 0(t3)
  	jr	t3

  clr_sw_int:
          RVMODEL_CLEAR_MSW_INT
          j       resto_rtn

  clr_tmr_int:
          RVMODEL_CLEAR_MTIMER_INT
          j       resto_rtn

  clr_ext_int:
          RVMODEL_CLEAR_MEXT_INT
          SREG      t3, -3*REGWIDTH(t1) /* save 4rd sig value, (intID)  */
          j       resto_rtn
  .align 3
  clrint_tbl:
  	.dword	resto_rtn	/* int cause 0 is reserved, just return */
  	.dword	clr_sw_int	/* int cause 1  Smode SW int            */
  	.dword	resto_rtn	/* int cause 2 is reserved, just return */
  	.dword	clr_sw_int	/* int cause 3  Mmode SW int            */
  	.dword	resto_rtn	/* int cause 4 is reserved, just return */
  	.dword	clr_tmr_int	/* int cause 5  Smode Tmr int           */
  	.dword	resto_rtn	/* int cause 6 is reserved, just return */
  	.dword	clr_tmr_int	/* int cause 7  Mmode Tmr int           */
  	.dword	resto_rtn	/* int cause 8 is reserved, just return */
  	.dword	clr_ext_int	/* int cause 9  Smode Ext int           */
  	.dword	resto_rtn	/* int cause A is reserved, just return */
  	.dword	clr_ext_int	/* int cause B  Mmode Ext int           */
  	.dword	resto_rtn	/* int cause C is reserved, just return */
  	.dword	resto_rtn	/* int cause D is reserved, just return */
  	.dword	resto_rtn	/* int cause E is reserved, just return */
  	.dword	resto_rtn	/* int cause F is reserved, just return */
  	.dword	resto_rtn	/* int cause 10 is reserved, just return */
  	.dword	resto_rtn	/* int cause 11 is reserved, just return */
  	.dword	resto_rtn	/* int cause 12 is reserved, just return */
  	.dword	resto_rtn	/* int cause 13 is reserved, just return */
  	.dword	resto_rtn	/* int cause 14 is reserved, just return */
  	.dword	resto_rtn	/* int cause 15 is reserved, just return */
  	.dword	resto_rtn	/* int cause 16 is reserved, just return */
  	.dword	resto_rtn	/* int cause 17 is reserved, just return */
  	.dword	resto_rtn	/* int cause 18 is reserved, just return */
  	.dword	resto_rtn	/* int cause 19 is reserved, just return */
  	.dword	resto_rtn	/* int cause 1A is reserved, just return */
  	.dword	resto_rtn	/* int cause 1B is reserved, just return */
  	.dword	resto_rtn	/* int cause 1C is reserved, just return */
  	.dword	resto_rtn	/* int cause 1D is reserved, just return */
  	.dword	resto_rtn	/* int cause 1E is reserved, just return */
  	.dword	resto_rtn	/* int cause 1F is reserved, just return */

  1:	// xtvec_installed:
  ret

  // ----------------------------------------------------------------------------------------------
  // ----------------------------------------------------------------------------------------------
  // ----------------------------------------------------------------------------------------------
  // ----------------------------------------------------------------------------------------------

  exit_cleanup://COMPLIANCE_HALT should get here
  	la	t3, tramptbl_sv+ NUM_SPECD_INTCAUSES*4	// end of save area

  	la	t5, mtvec_save
  	LREG	t1, 8(t5)
  	csrw	 CSR_MSCRATCH, t1		        // restore mscratch
  	LREG	t4, 0(t5)		              // load orig mtvec
  	csrrw	t2, CSR_MTVEC, t4		        // restore mtvec (not redundant)
  	bne	t4, t2, 1f// if saved!=mtvec, done, else need to restore

  	addi	t2, t4, NUM_SPECD_INTCAUSES*4  // start pt is end of vect area
  resto_vec:	                              // goes backwards, t2= dest vec tbl ptr,
                                            // t3=src save area ptr, t4=vec tbl begin
  	lw	t6, 0(t3)		                        // read saved tgt entry
  	sw	t6, 0(t2)		                        // restore original tgt
  	addi	t2, t2, -4		                    // prev tgt  index
  	addi	t3, t3, -4		                    // prev save index
  	bne	t2, t4, resto_vec	                  // didn't get to end, continue
  1:
  rvtest_end:
  .option pop
#endif
#ifdef rvtest_gpr_save
  csrw CSR_MSCRATCH, x31       //save x31, get temp pointer
  LA(x31, gpr_save)
  SREG x0, 0*REGWIDTH(x31)
  SREG x1, 1*REGWIDTH(x31)
  SREG x2, 2*REGWIDTH(x31)
  SREG x3, 3*REGWIDTH(x31)
  SREG x4, 4*REGWIDTH(x31)
  SREG x5, 5*REGWIDTH(x31)
  SREG x6, 6*REGWIDTH(x31)
  SREG x7, 7*REGWIDTH(x31)
  SREG x8, 8*REGWIDTH(x31)
  SREG x9, 9*REGWIDTH(x31)
  SREG x10, 10*REGWIDTH(x31)
  SREG x11, 11*REGWIDTH(x31)
  SREG x12, 12*REGWIDTH(x31)
  SREG x13, 13*REGWIDTH(x31)
  SREG x14, 14*REGWIDTH(x31)
  SREG x15, 15*REGWIDTH(x31)
  SREG x16, 16*REGWIDTH(x31)
  SREG x17, 17*REGWIDTH(x31)
  SREG x18, 18*REGWIDTH(x31)
  SREG x19, 19*REGWIDTH(x31)
  SREG x20, 20*REGWIDTH(x31)
  SREG x21, 21*REGWIDTH(x31)
  SREG x22, 22*REGWIDTH(x31)
  SREG x23, 23*REGWIDTH(x31)
  SREG x24, 24*REGWIDTH(x31)
  SREG x25, 25*REGWIDTH(x31)
  SREG x26, 26*REGWIDTH(x31)
  SREG x27, 27*REGWIDTH(x31)
  SREG x28, 28*REGWIDTH(x31)
  SREG x29, 29*REGWIDTH(x31)
  SREG x30, 30*REGWIDTH(x31)
  addi x30, x31, 0                // mv gpr pointer to x30
  csrr x31, CSR_MSCRATCH              // restore value of x31
  SREG x31, 31*REGWIDTH(x30)      // store x31
#endif
  tail sc_exit
.endm


.macro RVTEST_DATA_BEGIN
.data
.align 4
.global rvtest_data_begin
rvtest_data_begin:
#ifdef rvtest_mtrap_routine
trapreg_sv:
      .fill    7, REGWIDTH, 0xdeadbeef     /* handler reg save area, 1 extra wd just in case */
tramptbl_sv:	// save area of existing trampoline table
.rept NUM_SPECD_INTCAUSES
	J	.+0		  /* prototype jump instruction, offset to be filled in */
.endr
mtvec_save:
	.dword	0		  /* save area for incoming mtvec */
mscratch_save:
	.dword  0		  /* save area for incoming mscratch */
#endif

.endm

.macro RVTEST_DATA_END
.global rvtest_data_end
rvtest_data_end:
.endm


#define RVTEST_CASE(_PNAME,_DSTR,...)

#define RVTEST_SIGBASE(_R,_TAG) \
  LA(_R,_TAG);\
  .set offset,0;

.set offset,0;
#define _ARG5(_1ST,_2ND, _3RD,_4TH,_5TH,...) _5TH
#define _ARG4(_1ST,_2ND, _3RD,_4TH,...) _4TH
#define _ARG3(_1ST,_2ND, _3RD, ...) _3RD
#define _ARG2(_1ST,_2ND, ...) _2ND
#define _ARG1(_1ST,...) _1ST
#define NARG(...) _ARG5(__VA_OPT__(__VA_ARGS__,)4,3,2,1,0)
#define RVTEST_SIGUPD(_BR,_R,...)\
  .if NARG(__VA_ARGS__) == 1;\
    SREG _R,_ARG1(__VA_ARGS__,0)(_BR);\
    .set offset,_ARG1(__VA_OPT__(__VA_ARGS__,)0)+REGWIDTH;\
  .endif;\
  .if NARG(__VA_ARGS__) == 0;\
    SREG _R,offset(_BR);\
  .set offset,offset+REGWIDTH;\
  .endif;

/*
 * RVTEST_BASEUPD(base reg) - updates the base register the last signature address + REGWIDTH
 * RVTEST_BASEUPD(base reg, new reg) - moves value of the next signature region to update into new reg
 * The hidden variable offset is reset always
*/

#define RVTEST_BASEUPD(_BR,...)\
    .if NARG(__VA_ARGS__) == 0;\
        addi _BR,_BR,offset;\
    .endif;\
    .if NARG(__VA_ARGS__) == 1;\
        addi _ARG1(__VA_ARGS__,x0),_BR,offset;\
    .endif;\
    .set offset,0;



//------------------------------ BORROWED FROM ANDREW's RISC-V TEST MACROS -----------------------//
#define MASK_XLEN(x) ((x) & ((1 << (__riscv_xlen - 1) << 1) - 1))

#define SEXT_IMM(x) ((x) | (-(((x) >> 11) & 1) << 11))

#define TEST_JALR_OP(tempreg, rd, rs1, imm, swreg, offset,adj) \
5:                                            ;\
    LA(rd,5b                                 ) ;\
    .if adj & 1 == 1                          ;\
    LA(rs1, 3f-imm+adj-1  )                    ;\
    jalr rd, imm+1(rs1)                      ;\
    .else                                     ;\
    LA(rs1, 3f-imm+adj)                        ;\
    jalr rd, imm(rs1)                         ;\
    .endif                                    ;\
    nop                                       ;\
    nop                                       ;\
    xori rd,rd, 0x2                           ;\
    j 4f                                      ;\
                                              ;\
3:  .if adj & 2 == 2                              ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    xori rd,rd, 0x3                           ;\
    j 4f                                      ;\
    .if adj&2 == 2                              ;\
    .fill 2,1,0x00                     ;\
    .endif                                    ;\
                                              ;\
4: LA(tempreg, 5b                            ) ;\
   andi tempreg,tempreg,~(3)                  ;\
    sub rd,rd,tempreg                          ;\
    RVTEST_SIGUPD(swreg,rd,offset)
//SREG rd, offset(swreg);

#define TEST_JAL_OP(tempreg, rd, imm, label, swreg, offset, adj)\
5:                                           ;\
    LA(tempreg, 2f                          ) ;\
    jalr x0,0(tempreg)                       ;\
6:  LA(tempreg, 4f                          ) ;\
    jalr x0,0(tempreg)                        ;\
1:  .if adj & 2 == 2                         ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    xori rd,rd, 0x1                           ;\
    beq x0,x0,6b                               ;\
    .if adj & 2 == 2                              ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    .if (imm/2) - 2 >= 0                      ;\
        .set num,(imm/2)-2                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 3f                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    nop                                       ;\
    .endr                                     ;\
                                              ;\
2:  jal rd, label+(adj)                    ;\
    .if adj & 2 == 2                              ;\
    nop                                       ;\
    nop                                       ;\
    .endif                                    ;\
    xori rd,rd, 0x2                           ;\
    j 4f                                      ;\
    .if (imm/2) - 3 >= 0                      ;\
        .set num,(imm/2)-3                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
    .if label == 1b                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    nop                                       ;\
    .endr                                     ;\
3:  .if adj & 2 == 2                              ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    xori rd,rd, 0x3                           ;\
    LA(tempreg, 4f                          ) ;\
    jalr x0,0(tempreg)                        ;\
    .if adj&2 == 2                              ;\
    .fill 2,1,0x00                     ;\
    .endif                                    ;\
4: LA(tempreg, 5b                            ) ;\
   andi tempreg,tempreg,~(3)                  ;\
    sub rd,rd,tempreg                          ;\
    RVTEST_SIGUPD(swreg,rd,offset)
//SREG rd, offset(swreg);

#define TEST_BRANCH_OP(inst, tempreg, reg1, reg2, val1, val2, imm, label, swreg, offset,adj) \
    LI(reg1, MASK_XLEN(val1))                  ;\
    LI(reg2, MASK_XLEN(val2))                  ;\
    addi tempreg,x0,0                         ;\
    j 2f                                      ;\
                                              ;\
1:  .if adj & 2 == 2                         ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    addi tempreg,tempreg, 0x1                           ;\
    j 4f                                      ;\
    .if adj & 2 == 2                              ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    .if (imm/2) - 2 >= 0                      ;\
        .set num,(imm/2)-2                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 3f                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    nop                                       ;\
    .endr                                     ;\
                                              ;\
2:  inst reg1, reg2, label+adj                ;\
    addi tempreg, tempreg,0x2                   ;\
    j 4f                                      ;\
    .if (imm/4) - 3 >= 0                      ;\
        .set num,(imm/4)-3                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 1b                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    nop                                       ;\
    .endr                                     ;\
                                              ;\
3:  .if adj & 2 == 2                              ;\
    .fill 2,1,0x00                          ;\
    .endif                                    ;\
    addi tempreg, tempreg,0x3                           ;\
    j 4f                                      ;\
    .if adj&2 == 2                              ;\
    .fill 2,1,0x00                     ;\
    .endif                                    ;\
                                              ;\
4:   RVTEST_SIGUPD(swreg,tempreg,offset)
//SREG tempreg, offset(swreg);

#define TEST_STORE(swreg,testreg,index,rs1,rs2,rs2_val,imm_val,offset,inst,adj)   ;\
LI(rs2,rs2_val)                                                             ;\
addi rs1,swreg,offset+adj                                                     ;\
LI(testreg,imm_val)                                                         ;\
sub rs1,rs1,testreg                                                          ;\
inst rs2, imm_val(rs1)                                                      ;\
nop                                                                         ;\
nop

#define TEST_LOAD(swreg,testreg,index,rs1,destreg,imm_val,offset,inst,adj)   ;\
LA(rs1,rvtest_data+(index*4)+adj-imm_val)                                      ;\
inst destreg, imm_val(rs1)                                                   ;\
nop                                                                         ;\
nop                                                                         ;\
RVTEST_SIGUPD(swreg,destreg,offset)
//SREG destreg, offset(swreg);

#define TEST_CSR_FIELD(ADDRESS,TEMP_REG,MASK_REG,NEG_MASK_REG,VAL,DEST_REG,OFFSET,BASE_REG) \
    LI(TEMP_REG,VAL);\
    and TEMP_REG,TEMP_REG,MASK_REG;\
    csrr DEST_REG,ADDRESS;\
    and DEST_REG,DEST_REG,NEG_MASK_REG;\
    or TEMP_REG,TEMP_REG,DEST_REG;\
    csrw ADDRESS,TEMP_REG;\
    csrr DEST_REG,ADDRESS;\
    RVTEST_SIGUPD(BASE_REG,DEST_REG,OFFSET)


#define TEST_CASE(testreg, destreg, correctval, swreg, offset, code... ) \
    code; \
    RVTEST_SIGUPD(swreg,destreg,offset); \
    RVMODEL_IO_ASSERT_GPR_EQ(testreg, destreg, correctval)

#define TEST_AUIPC(inst, destreg, correctval, imm, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LA testreg, 1f; \
      1: \
      inst destreg, imm; \
      sub destreg, destreg, testreg; \
      )

//Tests for a instructions with register-immediate operand
#define TEST_IMM_OP( inst, destreg, reg, correctval, val, imm, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(reg, MASK_XLEN(val)); \
      inst destreg, reg, SEXT_IMM(imm); \
    )

//Tests for a instructions with register-register operand
#define TEST_RRI_OP(inst, destreg, reg1, reg2, imm, correctval, val1, val2, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(reg1, MASK_XLEN(val1)); \
      LI(reg2, MASK_XLEN(val2)); \
      inst destreg, reg1, reg2, imm; \
    )

//Tests for a instructions with register-register operand
#define TEST_RI_OP(inst, destreg, reg2, imm, correctval, val1, val2, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(destreg, MASK_XLEN(val1)); \
      LI(reg2, MASK_XLEN(val2)); \
      inst destreg, reg2, imm; \
    )

//Tests for a instructions with register-register operand
#define TEST_RR_OP(inst, destreg, reg1, reg2, correctval, val1, val2, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(reg1, MASK_XLEN(val1)); \
      LI(reg2, MASK_XLEN(val2)); \
      inst destreg, reg1, reg2; \
    )

#define TEST_CNOP_OP( inst, testreg, imm_val, swreg, offset) \
    TEST_CASE(testreg, x0, 0, swreg, offset, \
      inst imm_val; \
      )

#define TEST_CMV_OP( inst, destreg, reg, correctval, val2, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(reg, MASK_XLEN(val2)); \
      inst destreg, reg; \
      )

#define TEST_CR_OP( inst, destreg, reg, correctval, val1, val2, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(reg, MASK_XLEN(val2)); \
      LI(destreg, MASK_XLEN(val1)); \
      inst destreg, reg; \
      )

#define TEST_CI_OP( inst, destreg, correctval, val, imm, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(destreg, MASK_XLEN(val)); \
      inst destreg, imm; \
      )

#define TEST_CADDI4SPN_OP( inst, destreg, correctval, imm, swreg, offset, testreg) \
    TEST_CASE(testreg, destreg, correctval, swreg, offset, \
      LI(x2, 0); \
      inst destreg, x2,imm; \
      )

#define TEST_CBRANCH_OP(inst, tempreg, reg2, val2, imm, label, swreg, offset) \
    LI(reg2, MASK_XLEN(val2))                  ;\
    j 2f                                      ;\
    addi tempreg, x0,0                        ;\
    .option push                              ;\
    .option norvc                             ;\
1:  addi tempreg, tempreg,0x1                 ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 4 >= 0                      ;\
        .set num,(imm/2)-4                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
    .if label == 3f                           ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
2:  inst reg2, label                          ;\
    .option push                              ;\
    .option norvc                             ;\
    addi tempreg, tempreg, 0x2                ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 5 >= 0                      ;\
        .set num,(imm/2)-5                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 1b                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
                                              ;\
3:  addi tempreg, tempreg ,0x3                ;\
                                              ;\
4:  RVTEST_SIGUPD(swreg,tempreg,offset)
//SREG tempreg, offset(swreg);


#define TEST_CJ_OP(inst, tempreg, imm, label, swreg, offset) \
    .option push                              ;\
    .option norvc                             ;\
    j 2f                                      ;\
    addi tempreg,x0,0                         ;\
1:  addi tempreg, tempreg,0x1                 ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 4 >= 0                      ;\
        .set num,(imm/2)-4                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
    .if label == 3f                           ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
2:  inst label                          ;\
    .option push                              ;\
    .option norvc                             ;\
    addi tempreg, tempreg, 0x2                           ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 5 >= 0                      ;\
        .set num,(imm/2)-5                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 1b                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
                                              ;\
3:  addi tempreg, tempreg, 0x3                ;\
                                              ;\
4:  RVTEST_SIGUPD(swreg,tempreg,offset)
//SREG tempreg, offset(swreg);

#define TEST_CJAL_OP(inst, tempreg, imm, label, swreg, offset) \
5:                                            ;\
    j 2f                                      ;\
                                              ;\
    .option push                              ;\
    .option norvc                             ;\
1:  xori x1,x1, 0x1                           ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 4 >= 0                      ;\
        .set num,(imm/2)-4                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
    .if label == 3f                           ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
2:  inst label                          ;\
    .option push                              ;\
    .option norvc                             ;\
    xori x1,x1, 0x2                           ;\
    j 4f                                      ;\
    .option pop                               ;\
    .if (imm/2) - 5 >= 0                      ;\
        .set num,(imm/2)-5                    ;\
    .else                                     ;\
        .set num,0                            ;\
    .endif                                    ;\
     .if label == 1b                          ;\
        .set num,0                            ;\
    .endif                                    ;\
    .rept num                                 ;\
    c.nop                                     ;\
    .endr                                     ;\
                                              ;\
3:  xori x1,x1, 0x3                           ;\
                                              ;\
4: LA(tempreg, 5b)                             ;\
   andi tempreg,tempreg,~(3)                  ;\
    sub x1,x1,tempreg                          ;\
  RVTEST_SIGUPD(swreg,x1,offset)
//SREG x1, offset(swreg);

#define TEST_CJR_OP(tempreg, rs1, swreg, offset) \
5:                                            ;\
    LA(rs1, 3f)                                ;\
                                              ;\
2:  c.jr rs1                                  ;\
    xori rs1,rs1, 0x2                           ;\
    j 4f                                      ;\
                                              ;\
3:  xori rs1,rs1, 0x3                           ;\
                                              ;\
4: LA(tempreg, 5b)                             ;\
   andi tempreg,tempreg,~(3)                  ;\
    sub rs1,rs1,tempreg                          ;\
    RVTEST_SIGUPD(swreg,rs1,offset)
//SREG rs1, offset(swreg);

#define TEST_CJALR_OP(tempreg, rs1, swreg, offset) \
5:                                            ;\
    LA(rs1, 3f                               ) ;\
                                              ;\
2:  c.jalr rs1                                  ;\
    xori x1,x1, 0x2                           ;\
    j 4f                                      ;\
                                              ;\
3:  xori x1,x1, 0x3                           ;\
                                              ;\
4: LA(tempreg, 5b                            ) ;\
   andi tempreg,tempreg,~(3)                  ;\
    sub x1,x1,tempreg                          ;\
    RVTEST_SIGUPD(swreg,x1,offset)
//SREG x1, offset(swreg);


//--------------------------------- Migration aliases ------------------------------------------
#ifdef RV_COMPLIANCE_RV32M
  #warning "RV_COMPLIANCE_RV32M macro will be deprecated."
  #define RVMODEL_BOOT \
    RVTEST_IO_INIT; \
    RV_COMPLIANCE_RV32M ; \
    RV_COMPLIANCE_CODE_BEGIN
#endif

#define SWSIG(a, b)

#ifdef RV_COMPLIANCE_DATA_BEGIN
  #warning "RV_COMPLIANCE_DATA_BEGIN macro deprecated in v0.2. Please use RVMODEL_DATA_BEGIN instead"
  #define RVMODEL_DATA_BEGIN \
    RV_COMPLIANCE_DATA_BEGIN
#endif

#ifdef RV_COMPLIANCE_DATA_END
  #warning "RV_COMPLIANCE_DATA_END macro deprecated in v0.2. Please use RVMODEL_DATA_END instead"
  #define RVMODEL_DATA_END \
    RV_COMPLIANCE_DATA_END
#endif

#ifdef RV_COMPLIANCE_HALT
  #warning "RV_COMPLIANCE_HALT macro deprecated in v0.2. Please use RVMODEL_HALT instead"
  #define RVMODEL_HALT \
    RV_COMPLIANCE_HALT
#endif

#ifdef RVTEST_IO_ASSERT_GPR_EQ
  #warning "RVTEST_IO_ASSERT_GPR_EQ macro deprecated in v0.2. Please use RVMODEL_IO_ASSERT_GPR_EQ instead"
  #define RVMODEL_IO_ASSERT_GPR_EQ(_SP, _R, _I) \
    RVTEST_IO_ASSERT_GPR_EQ(_SP,_R, _I)
#endif

#ifdef RVTEST_IO_WRITE_STR
  #warning "RVTEST_IO_WRITE_STR macro deprecated in v0.2. Please use RVMODEL_IO_WRITE_STR instead"
  #define RVMODEL_IO_WRITE_STR(_SP, _STR) \
    RVTEST_IO_WRITE_STR(_SP, _STR)
#endif

#ifdef RVTEST_IO_INIT
  #warning "RVTEST_IO_INIT is deprecated in v0.2. Please use RVMODEL_BOOT for initialization"
#endif

#ifdef RVTEST_IO_CHECK
  #warning "RVTEST_IO_CHECK is deprecated in v0.2.
#endif

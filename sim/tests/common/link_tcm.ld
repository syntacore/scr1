/*
* Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
* @file       <link.ld>
* @brief      bare metal tests' linker script
*/

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY {
  RAM (rwx) : ORIGIN = 0x0, LENGTH = 64K
  TCM (rwx) : ORIGIN = 0x00480000, LENGTH = 64K
}

STACK_SIZE = 1024;

CL_SIZE = 32;

SECTIONS {

  /* code segment */
  .text.init ORIGIN(RAM) : { 
    FILL(0);
    . = 0x100 - 12;
    SIM_EXIT = .;
    LONG(0x13);
    SIM_STOP = .;
    LONG(0x6F);
    LONG(-1);
    . = 0x100;
    *crt_tcm.o(.text .text.*)
    *(.text.init)
    . = ALIGN(CL_SIZE);
  } >RAM

  __reloc_start = .;

  .text : {
    PROVIDE(__TEXT_START__ = .);
    *(.text .text.*)
    *(sc_test_section)
    . = ALIGN(CL_SIZE);
     PROVIDE(__TEXT_END__ = .);
  } >TCM AT>RAM

  .rodata ALIGN(CL_SIZE) : {
    __global_pointer$ = . + 0x800;
    *(.rodata) *(.rodata.*) *(.gnu.linkonce.r.*)
    . = ALIGN(CL_SIZE);
    LONG(0x13);
    . = ALIGN(CL_SIZE);
  } >TCM AT>RAM


  /* data segment */
  .data ALIGN(CL_SIZE) : {
    PROVIDE(__DATA_START__ = .);
    *(.data .data.*)
    . = ALIGN(CL_SIZE);
  } >TCM AT>RAM

  
  .sdata ALIGN(CL_SIZE) : {
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
    . = ALIGN(CL_SIZE);
    PROVIDE(__DATA_END__ = .);
  } >TCM AT>RAM

  /* thread-local data segment */
  .tdata ALIGN(CL_SIZE) : {
    PROVIDE(_tls_data = .);
    PROVIDE(_tdata_begin = .);
    *(.tdata .tdata.*)
    PROVIDE(_tdata_end = .);
    . = ALIGN(CL_SIZE);
  } >TCM AT>RAM

  .tbss ALIGN(CL_SIZE) : {
    PROVIDE(_tbss_begin = .);
    *(.tbss .tbss.*)
    . = ALIGN(CL_SIZE);
    PROVIDE(_tbss_end = .);
  } >TCM AT>RAM

  /* bss segment */
  .sbss ALIGN(CL_SIZE) : {
    PROVIDE(__BSS_START__ = .);
    *(.sbss .sbss.* .gnu.linkonce.sb.*)
    *(.scommon)
    . = ALIGN(CL_SIZE);
  } >TCM AT>RAM

  .bss ALIGN(CL_SIZE) : {
    *(.dynbss) *(.bss .bss.* .gnu.linkonce.b.*) *(COMMON)
    . = ALIGN(CL_SIZE);
    PROVIDE(__BSS_END__ = .);
  } >TCM AT>RAM

  _end = .;
  PROVIDE(__end = .);

  /* End of uninitalized data segement */

  .stack ORIGIN(TCM) + LENGTH(TCM) - STACK_SIZE : {
    PROVIDE(__STACK_START__ = .);
    . += STACK_SIZE;
    PROVIDE(__C_STACK_TOP__ = .);
    PROVIDE(__STACK_END__ = .);
  } >TCM

  /DISCARD/ : {
    *(.eh_frame .eh_frame.*)
  }
}

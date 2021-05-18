/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_ipic.svh>
/// @brief      IPIC header file
///

`ifndef SCR1_IPIC_SVH
`define SCR1_IPIC_SVH

`include "scr1_arch_description.svh"

`ifdef SCR1_IPIC_EN
//-------------------------------------------------------------------------------
// Parameters declaration
//-------------------------------------------------------------------------------
parameter                                   SCR1_IRQ_VECT_NUM       = 16;   // must be power of 2 in the current implementation
parameter                                   SCR1_IRQ_VECT_WIDTH     = $clog2(SCR1_IRQ_VECT_NUM+1);
parameter                                   SCR1_IRQ_LINES_NUM      = SCR1_IRQ_VECT_NUM;
parameter                                   SCR1_IRQ_LINES_WIDTH    = $clog2(SCR1_IRQ_LINES_NUM);
parameter   logic [SCR1_IRQ_VECT_WIDTH-1:0] SCR1_IRQ_VOID_VECT_NUM  = SCR1_IRQ_VECT_WIDTH'(SCR1_IRQ_VECT_NUM);
parameter                                   SCR1_IRQ_IDX_WIDTH      = $clog2(SCR1_IRQ_VECT_NUM);

// Address decoding parameters
parameter   logic [2:0]                     SCR1_IPIC_CISV          = 3'h0;    // RO
parameter   logic [2:0]                     SCR1_IPIC_CICSR         = 3'h1;    // {IP, IE}
parameter   logic [2:0]                     SCR1_IPIC_IPR           = 3'h2;    // RW1C
parameter   logic [2:0]                     SCR1_IPIC_ISVR          = 3'h3;    // RO
parameter   logic [2:0]                     SCR1_IPIC_EOI           = 3'h4;    // RZW
parameter   logic [2:0]                     SCR1_IPIC_SOI           = 3'h5;    // RZW
parameter   logic [2:0]                     SCR1_IPIC_IDX           = 3'h6;    // RW
parameter   logic [2:0]                     SCR1_IPIC_ICSR          = 3'h7;    // RW

parameter                                   SCR1_IPIC_ICSR_IP       = 0;
parameter                                   SCR1_IPIC_ICSR_IE       = 1;
parameter                                   SCR1_IPIC_ICSR_IM       = 2;
parameter                                   SCR1_IPIC_ICSR_INV      = 3;
parameter                                   SCR1_IPIC_ICSR_IS       = 4;
parameter                                   SCR1_IPIC_ICSR_PRV_LSB  = 8;
parameter                                   SCR1_IPIC_ICSR_PRV_MSB  = 9;
parameter                                   SCR1_IPIC_ICSR_LN_LSB   = 12;
parameter                                   SCR1_IPIC_ICSR_LN_MSB   = SCR1_IPIC_ICSR_LN_LSB
                                                                    + SCR1_IRQ_LINES_WIDTH;

parameter   logic [1:0]                     SCR1_IPIC_PRV_M         = 2'b11;

//-------------------------------------------------------------------------------
// Types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_CSR2IPIC_RD,
    SCR1_CSR2IPIC_WR
`ifdef SCR1_XPROP_EN
    ,
    SCR1_CSR2IPIC_ERROR = 'x
`endif // SCR1_XPROP_EN
} type_scr1_csr2ipic_wr_e;

`endif // SCR1_IPIC_EN
`endif // SCR1_IPIC_SVH

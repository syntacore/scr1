`ifndef SCR1_CSR_MAP_SVH
`define SCR1_CSR_MAP_SVH
/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_csr_map.svh>
/// @brief      CSR mapping/description file
///

`include "scr1_arch_description.svh"
`include "scr1_ipic.svh"

//-------------------------------------------------------------------------------
// CSR Addres register definition
//-------------------------------------------------------------------------------
//------- Machine CSR -------------
// Machine Information Registers (MRO)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MCPUID         = 'hF00;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MIMPID         = 'hF01;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MHARTID        = 'hF10;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MRTLID         = 'hFC0;
// Machine Trap Setup (MRW)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MSTATUS        = 'h300;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTVEC          = 'h301;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTDELEG        = 'h302;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MIE            = 'h304;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTIMECMP       = 'h321;
// Machine Timers and Counters (MRW)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTIME          = 'h701;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTIMEH         = 'h741;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MTIMECLKSET    = 'h7B4;
// Machine Trap Handling (MRW)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MSCRATCH       = 'h340;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MEPC           = 'h341;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MCAUSE         = 'h342;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MBADADDR       = 'h343;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MIP            = 'h344;
// Machine Protection and Translation (MRW)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MBASE          = 'h380;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MBOUND         = 'h381;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MIBASE         = 'h382;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MIBOUND        = 'h383;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MDBASE         = 'h384;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_MDBOUND        = 'h385;
//------- User CSR ----------------
// User Countes/Timers (RO)
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_CYCLE          = 'hC00;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_TIME           = 'hC01;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_INSTRET        = 'hC02;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_CYCLEH         = 'hC80;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_TIMEH          = 'hC81;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]  SCR1_CSR_ADDR_INSTRETH       = 'hC82;

//-------------------------------------------------------------------------------
// CSR register definition
//-------------------------------------------------------------------------------
// MCPUID
`define SCR1_RV_BASE_32I         2'b00
`define SCR1_RV_BASE_32E         2'b01
`define SCR1_RVC_ENC             `SCR1_XLEN'h00000004
`define SCR1_RVE_ENC             `SCR1_XLEN'h00000010
`define SCR1_RVI_ENC             `SCR1_XLEN'h00000100
`define SCR1_RVM_ENC             `SCR1_XLEN'h00001000
`ifndef SCR1_RVE_EXT
`define SCR1_RV_BASE             (`SCR1_RV_BASE_32I << (`SCR1_XLEN-2)) | `SCR1_RVI_ENC
`else // SCR1_RVE_EXT
`define SCR1_RV_BASE             (`SCR1_RV_BASE_32E << (`SCR1_XLEN-2)) | `SCR1_RVE_ENC
`endif // SCR1_RVE_EXT

`define SCR1_CSR_MCPUID     (  `SCR1_RV_BASE \
`ifdef SCR1_RVC_EXT                          \
                             | `SCR1_RVC_ENC \
`endif /* SCR1_RVC_EXT */                    \
`ifdef SCR1_RVM_EXT                          \
                             | `SCR1_RVM_ENC \
`endif /* SCR1_RVM_EXT */                    \
                             )

// MIMPID
parameter   bit [`SCR1_XLEN-1:0]    SCR1_CSR_MIMPID     = 'h16108000;
// MRTLID
parameter   bit [`SCR1_XLEN-1:0]    SCR1_CSR_MRTLID     = `SCR1_BUILD_ID;

// MSTATUS
parameter   bit [1:0]   SCR1_CSR_MSTATUS_PRV_VAL        = 2'b11;
parameter   bit         SCR1_CSR_MSTATUS_IE0_RST_VAL    = 1'b0;
parameter   bit         SCR1_CSR_MSTATUS_IE1_RST_VAL    = 1'b1;
parameter   bit         SCR1_CSR_MSTATUS_IE_PUSH_VAL    = 1'b0;
parameter   bit         SCR1_CSR_MSTATUS_IE_POP_VAL     = 1'b1;
parameter               SCR1_CSR_MSTATUS_IE0_OFFSET     = 0;
parameter               SCR1_CSR_MSTATUS_IE1_OFFSET     = 3;

// MTVEC
//`define SCR1_BOOT_UPPER_ADDR
`ifndef SCR1_BOOT_UPPER_ADDR
parameter   bit [`SCR1_XLEN-1:0]    SCR1_CSR_MTVEC      = 'h100;
parameter   bit [`SCR1_XLEN-1:0]    SCR1_MTRAP_VECTOR   = 'h1C0;
parameter   bit [`SCR1_XLEN-1:0]    SCR1_RST_VECTOR     = 'h200;
`else // SCR1_BOOT_UPPER_ADDR
parameter   bit [`SCR1_XLEN-1:0]    SCR1_CSR_MTVEC      = 'hFFFFFE00;
parameter   bit [`SCR1_XLEN-1:0]    SCR1_MTRAP_VECTOR   = 'hFFFFFEC0;
parameter   bit [`SCR1_XLEN-1:0]    SCR1_RST_VECTOR     = 'hFFFFFF00;
`endif // SCR1_BOOT_UPPER_ADDR

// MIE
parameter   bit     SCR1_CSR_MIE_MTIE_RST_VAL   = 1'b1;
parameter   bit     SCR1_CSR_MIE_MEIE_RST_VAL   = 1'b1;
parameter           SCR1_CSR_MIE_MTIE_OFFSET    = 7;
parameter           SCR1_CSR_MIE_MEIE_OFFSET    = 11;

// MTIMECLKSET
`ifdef SCR1_RVE_EXT
`define SCR1_CSR_REDUCED_CNT
`endif // SCR1_RVE_EXT
//`define SCR1_CSR_CNT_FLAG
parameter   SCR1_CSR_TIMECLK_CNT_WIDTH      = 16;
parameter   [SCR1_CSR_TIMECLK_CNT_WIDTH-1:0]    SCR1_CSR_MTIMECLKSET_RST_VAL    = 'h64;
`ifdef SCR1_CSR_CNT_FLAG
 `ifdef SCR1_CSR_REDUCED_CNT
parameter   SCR1_CSR_MTIMECLKSET_WIDTH              = SCR1_CSR_TIMECLK_CNT_WIDTH+2;
 `else // ~SCR1_CSR_REDUCED_CNT
parameter   SCR1_CSR_MTIMECLKSET_WIDTH              = SCR1_CSR_TIMECLK_CNT_WIDTH+4;
parameter   SCR1_CSR_MTIMECLKSET_CYCLE_STOP_OFFSET  = SCR1_CSR_TIMECLK_CNT_WIDTH+2;
parameter   SCR1_CSR_MTIMECLKSET_INSTRET_STOP_OFFSET= SCR1_CSR_TIMECLK_CNT_WIDTH+3;
 `endif // ~SCR1_CSR_REDUCED_CNT
parameter   SCR1_CSR_MTIMECLKSET_TIME_STOP_OFFSET   = SCR1_CSR_TIMECLK_CNT_WIDTH+1;
`else // ~SCR1_CSR_CNT_FLAG
parameter   SCR1_CSR_MTIMECLKSET_WIDTH              = SCR1_CSR_TIMECLK_CNT_WIDTH+1;
`endif // ~SCR1_CSR_CNT_FLAG
parameter   SCR1_CSR_MTIMECLKSET_RTC_INT_OFFSET     = SCR1_CSR_TIMECLK_CNT_WIDTH;

// MCAUSE
parameter   SCR1_CSR_MCAUSE_EC_WIDTH        = 4;
parameter   SCR1_CSR_MCAUSE_GAP_WIDTH       = `SCR1_XLEN-(SCR1_CSR_MCAUSE_EC_WIDTH+1);
// Exception code
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_IADDR_MSALL = 'd0;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_IACC_FAULT  = 'd1;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_ILL_INST    = 'd2;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_BREAKPOINT  = 'd3;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_LADDR_MSALL = 'd4;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_LACC_FAULT  = 'd5;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_SADDR_MSALL = 'd6;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_SACC_FAULT  = 'd7;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_MMODE_ECALL = 'd11;
// Interupt code
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_MTIRQ       = 'd7;
parameter   [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]  SCR1_CSR_MCAUSE_MEIRQ       = 'd11;

// TIME, INSTRET, CYCLE
`ifdef SCR1_CSR_REDUCED_CNT
parameter   SCR1_CSR_COUNTERS_WIDTH     = `SCR1_XLEN;
`else // ~SCR1_CSR_REDUCED_CNT
parameter   SCR1_CSR_COUNTERS_WIDTH     = 64;
`endif // ~SCR1_CSR_REDUCED_CNT

`ifdef SCR1_IPIC_EN
// IPIC
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_BASE      = 'h790;
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_CISV      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_CISV );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_CICSR     = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_CICSR);
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_IPR       = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_IPR  );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_ISVR      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_ISVR );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_EOI       = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_EOI  );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_SOI       = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_SOI  );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_IDX       = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_IDX  );
parameter   [SCR1_CSR_ADDR_WIDTH-1:0]      SCR1_CSR_ADDR_IPIC_ICSR      = (SCR1_CSR_ADDR_IPIC_BASE + SCR1_IPIC_ICSR );
`endif // SCR1_IPIC_EN

`ifdef SCR1_BRKM_EN
// BRKM
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0]     SCR1_CSR_ADDR_BRKM_MBASE    = 'h780;
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0]     SCR1_CSR_ADDR_BRKM_MSPAN    = 'h008;   // Must be power of 2
`endif // SCR1_BRKM_EN

`ifdef SCR1_DBGC_EN
// DBGC
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0]     SCR1_CSR_ADDR_DBGC_SCRATCH  = 'h788;
`endif // SCR1_DBGC_EN

//-------------------------------------------------------------------------------
// Types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_CSR_RESP_OK,
    SCR1_CSR_RESP_ER,
    SCR1_CSR_RESP_ERROR = 'x
} type_scr1_csr_resp_e;

`endif // SCR1_CSR_MAP_SVH

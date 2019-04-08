/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_pipe_csr.sv>
/// @brief      Control Status Registers (CSR)
///

`include "scr1_arch_description.svh"
`include "scr1_csr.svh"
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBGC_EN
`include "scr1_hdu.svh"
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
`include "scr1_tdu.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_csr (
    // Common
    input   logic                                       rst_n,
    input   logic                                       clk,
`ifdef SCR1_CLKCTRL_EN
    input   logic                                       clk_alw_on,
`endif // SCR1_CLKCTRL_EN

    // EXU <-> CSR read/write interface
    input   logic                                       exu2csr_r_req,          // CSR read/write address
    input   logic [SCR1_CSR_ADDR_WIDTH-1:0]             exu2csr_rw_addr,        // CSR read request
    output  logic [`SCR1_XLEN-1:0]                      csr2exu_r_data,         // CSR read data
    input   logic                                       exu2csr_w_req,          // CSR write request
    input   type_scr1_csr_cmd_sel_e                     exu2csr_w_cmd,          // CSR write command
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_w_data,         // CSR write data
    output  logic                                       csr2exu_rw_exc,         // CSR read/write access exception

    // EXU <-> CSR event interface
    input   logic                                       exu2csr_take_irq,       // Take IRQ trap
    input   logic                                       exu2csr_take_exc,       // Take exception trap
    input   logic                                       exu2csr_mret_update,    // MRET update CSR
    input   logic                                       exu2csr_mret_instr,     // MRET instruction
`ifdef SCR1_DBGC_EN
    input   logic                                       exu_no_commit,          // Forbid instruction commitment
`endif // SCR1_DBGC_EN
    input   type_scr1_exc_code_e                        exu2csr_exc_code,       // Exception code (see scr1_arch_types.svh)
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_trap_val,       // Trap value
    output  logic [`SCR1_XLEN-1:0]                      csr2exu_new_pc,         // Exception/IRQ/MRET new PC
    output  logic                                       csr2exu_irq,            // IRQ request
    output  logic                                       csr2exu_ip_ie,          // Some IRQ pending and locally enabled
    output  logic                                       csr2exu_mstatus_mie_up, // MSTATUS or MIE update in the current cycle

`ifdef SCR1_IPIC_EN
    // CSR <-> IPIC interface
    output  logic                                       csr2ipic_r_req,         // IPIC read request
    output  logic                                       csr2ipic_w_req,         // IPIC write request
    output  logic [2:0]                                 csr2ipic_addr,          // IPIC address
    output  logic [`SCR1_XLEN-1:0]                      csr2ipic_wdata,         // IPIC write data
    input   logic [`SCR1_XLEN-1:0]                      ipic2csr_rdata,         // IPIC read data
`endif // SCR1_IPIC_EN

    // CSR <-> PC interface
    input   logic [`SCR1_XLEN-1:0]                      curr_pc,                // Current PC
    input   logic [`SCR1_XLEN-1:0]                      next_pc,                // Next PC
`ifndef SCR1_CSR_REDUCED_CNT
    input   logic                                       instret_nexc,           // Instruction retired (without exception)
`endif // SCR1_CSR_REDUCED_CNT

    // IRQ
    input   logic                                       ext_irq,                // External interrupt request
    input   logic                                       soft_irq,               // Software interrupt request

    // Memory-mapped external timer
    input   logic                                       timer_irq,              // External timer interrupt request
    input   logic [63:0]                                mtime_ext,              // External timer value

`ifdef SCR1_DBGC_EN
    // CSR <-> HDU interface
    output  logic                                       csr2hdu_req,           // Request to HDU
    output  type_scr1_csr_cmd_sel_e                     csr2hdu_cmd,           // HDU command
    output  logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]    csr2hdu_addr,          // HDU address
    output  logic [`SCR1_XLEN-1:0]                      csr2hdu_wdata,         // HDU write data
    input   logic [`SCR1_XLEN-1:0]                      hdu2csr_rdata,         // HDU read data
    input   type_scr1_csr_resp_e                        hdu2csr_resp,          // HDU response
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
    // CSR <-> TDU interface
    output  logic                                       csr2tdu_req,           // Request to TDU
    output  type_scr1_csr_cmd_sel_e                     csr2tdu_cmd,           // TDU command
    output  logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]        csr2tdu_addr,          // TDU address
    output  logic [`SCR1_XLEN-1:0]                      csr2tdu_wdata,         // TDU write data
    input   logic [`SCR1_XLEN-1:0]                      tdu2csr_rdata,         // TDU read data
    input   type_scr1_csr_resp_e                        tdu2csr_resp,          // TDU response
`endif // SCR1_BRKM_EN

    // MHARTID fuse
    input   logic [`SCR1_XLEN-1:0]                      fuse_mhartid            // MHARTID fuse
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Registers
logic [`SCR1_XLEN-1:0]                              csr_mstatus;        // Aggregated MSTATUS
logic [`SCR1_XLEN-1:0]                              csr_mie;            // Aggregated MIE
logic [`SCR1_XLEN-1:0]                              csr_mip;            // Aggregated MIP
logic                                               csr_mstatus_mie;    // MSTATUS: Global interrupt enable
logic                                               csr_mstatus_mpie;   // MSTATUS: Global interrupt enable prior to the trap
logic                                               csr_mie_mtie;       // MIE: Machine timer interrupt enable
logic                                               csr_mie_meie;       // MIE: Machine external interrupt enable
logic                                               csr_mie_msie;       // MIE: Machine software interrupt enable
logic [`SCR1_XLEN-1:0]                              csr_mscratch;       // MSCRATCH
`ifdef SCR1_RVC_EXT
logic [`SCR1_XLEN-1:1]                              csr_mepc;           // MEPC (RVC)
`else // ~SCR1_RVC_EXT
logic [`SCR1_XLEN-1:2]                              csr_mepc;           // MEPC
`endif // ~SCR1_RVC_EXT
logic                                               csr_mcause_i;       // MCAUSE: Interrupt
type_scr1_exc_code_e                                csr_mcause_ec;      // MCAUSE: Exception code
type_scr1_exc_code_e                                csr_mcause_ec_new;
logic [`SCR1_XLEN-1:0]                              csr_mtval;          // MTVAL
logic [`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS]  csr_mtvec_base;     // MTVEC: Base (upper 26 bits)
logic                                               csr_mtvec_mode;     // MTVEC: Mode (0-direct, 1-vectored)
logic                                               csr_mip_mtip;       // MIP: Machine timer interrupt pending
logic                                               csr_mip_meip;       // MIP: Machine external interrupt pending
logic                                               csr_mip_msip;       // MIP: Machine software interrupt pending

`ifndef SCR1_CSR_REDUCED_CNT

logic [SCR1_CSR_COUNTERS_WIDTH-1:0]                 csr_instret;        // INSTRET
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_instret_hi;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_instret_hi_new;
logic [7:0]                                         csr_instret_lo;
logic [7:0]                                         csr_instret_lo_new;

logic [SCR1_CSR_COUNTERS_WIDTH-1:0]                 csr_cycle;          // CYCLE
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_cycle_hi;
logic [SCR1_CSR_COUNTERS_WIDTH-1:8]                 csr_cycle_hi_new;
logic [7:0]                                         csr_cycle_lo;
logic [7:0]                                         csr_cycle_lo_new;

`endif // ~SCR1_CSR_REDUCED_CNT

`ifdef SCR1_CSR_MCOUNTEN_EN
logic [`SCR1_XLEN-1:0]                              csr_mcounten;       // Aggregated MCOUNTEN
logic                                               csr_mcounten_cy;    // Cycle count enable
logic                                               csr_mcounten_ir;    // Instret count enable
`endif // SCR1_CSR_MCOUNTEN_EN

// Read signals
logic [`SCR1_XLEN-1:0]                              csr_r_data;
logic                                               csr_r_exc;

// Write signals
logic                                               csr_mstatus_up;
logic                                               csr_mie_up;
logic                                               csr_mscratch_up;
logic                                               csr_mepc_up;
logic                                               csr_mcause_up;
logic                                               csr_mtval_up;
logic                                               csr_mtvec_up;
`ifndef SCR1_CSR_REDUCED_CNT
logic [1:0]                                         csr_cycle_up;
logic [1:0]                                         csr_instret_up;
logic                                               csr_cycle_inc_lo;
logic                                               csr_cycle_inc_hi;
logic                                               csr_instret_inc_lo;
logic                                               csr_instret_inc_hi;
`endif // SCR1_CSR_REDUCED_CNT

`ifdef SCR1_CSR_MCOUNTEN_EN
logic                                               csr_mcounten_up;
`endif // SCR1_CSR_MCOUNTEN_EN

logic [`SCR1_XLEN-1:0]                              csr_w_data;
logic                                               csr_w_exc;

// Events
logic                                               e_exc;              // Successful exception trap
logic                                               e_irq;              // Successful IRQ trap
logic                                               e_mret;             // MRET instruction

`ifdef SCR1_DBGC_EN
logic                                               csr_hdu_req;
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
logic                                               csr_brkm_req;
`endif // SCR1_BRKM_EN


//-------------------------------------------------------------------------------
// Read CSR
//-------------------------------------------------------------------------------

// Aggregated CSRs
always_comb begin
    csr_mstatus     = '0;
    csr_mie         = '0;
    csr_mip         = '0;
`ifdef SCR1_CSR_MCOUNTEN_EN
    csr_mcounten    = '0;
`endif // SCR1_CSR_MCOUNTEN_EN

    csr_mstatus[SCR1_CSR_MSTATUS_MIE_OFFSET]                                = csr_mstatus_mie;
    csr_mstatus[SCR1_CSR_MSTATUS_MPIE_OFFSET]                               = csr_mstatus_mpie;
    csr_mstatus[SCR1_CSR_MSTATUS_MPP_OFFSET+1:SCR1_CSR_MSTATUS_MPP_OFFSET]  = SCR1_CSR_MSTATUS_MPP;

    csr_mie[SCR1_CSR_MIE_MSIE_OFFSET]   = csr_mie_msie;
    csr_mie[SCR1_CSR_MIE_MTIE_OFFSET]   = csr_mie_mtie;
    csr_mie[SCR1_CSR_MIE_MEIE_OFFSET]   = csr_mie_meie;

    csr_mip[SCR1_CSR_MIE_MSIE_OFFSET]   = csr_mip_msip;
    csr_mip[SCR1_CSR_MIE_MTIE_OFFSET]   = csr_mip_mtip;
    csr_mip[SCR1_CSR_MIE_MEIE_OFFSET]   = csr_mip_meip;

`ifdef SCR1_CSR_MCOUNTEN_EN
    csr_mcounten[SCR1_CSR_MCOUNTEN_CY_OFFSET]   = csr_mcounten_cy;
    csr_mcounten[SCR1_CSR_MCOUNTEN_IR_OFFSET]   = csr_mcounten_ir;
`endif // SCR1_CSR_MCOUNTEN_EN
end

always_comb begin
    csr_r_data      = '0;
    csr_r_exc       = 1'b0;
`ifdef SCR1_IPIC_EN
    csr2ipic_r_req  = 1'b0;
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBGC_EN
    csr_hdu_req    = 1'b0;
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
    csr_brkm_req   = 1'b0;
`endif // SCR1_BRKM_EN
    casez (exu2csr_rw_addr)
        // Machine Information Registers (read-only)
        SCR1_CSR_ADDR_MVENDORID : csr_r_data    = SCR1_CSR_MVENDORID;
        SCR1_CSR_ADDR_MARCHID   : csr_r_data    = SCR1_CSR_MARCHID;
        SCR1_CSR_ADDR_MIMPID    : csr_r_data    = SCR1_CSR_MIMPID;
        SCR1_CSR_ADDR_MHARTID   : csr_r_data    = fuse_mhartid;

        // Machine Trap Setup (read-write)
        SCR1_CSR_ADDR_MSTATUS   : csr_r_data    = csr_mstatus;
        SCR1_CSR_ADDR_MISA      : csr_r_data    = SCR1_CSR_MISA;
        SCR1_CSR_ADDR_MIE       : csr_r_data    = csr_mie;
        SCR1_CSR_ADDR_MTVEC     : csr_r_data    = {csr_mtvec_base, 4'd0, 2'(csr_mtvec_mode)};

        // Machine Trap Handling (read-write)
        SCR1_CSR_ADDR_MSCRATCH  : csr_r_data    = csr_mscratch;
        SCR1_CSR_ADDR_MEPC      : csr_r_data    =
`ifdef SCR1_RVC_EXT
                                                  {csr_mepc, 1'b0};
`else // SCR1_RVC_EXT
                                                  {csr_mepc, 2'b00};
`endif // SCR1_RVC_EXT

        SCR1_CSR_ADDR_MCAUSE    : csr_r_data    = {csr_mcause_i, type_scr1_csr_mcause_ec_v'(csr_mcause_ec)};
        SCR1_CSR_ADDR_MTVAL     : csr_r_data    = csr_mtval;
        SCR1_CSR_ADDR_MIP       : csr_r_data    = csr_mip;

        // User Counters/Timers (read-only)
        {SCR1_CSR_ADDR_HPMCOUNTER_MASK, 5'b?????}   : begin
            case (exu2csr_rw_addr[4:0])
                5'd1        : csr_r_data    = mtime_ext[31:0];
`ifndef SCR1_CSR_REDUCED_CNT
                5'd0        : csr_r_data    = csr_cycle[31:0];
                5'd2        : csr_r_data    = csr_instret[31:0];
`endif // SCR1_CSR_REDUCED_CNT
                default     : begin
                    // return 0
                end
            endcase
        end

        {SCR1_CSR_ADDR_HPMCOUNTERH_MASK, 5'b?????}  : begin
            case (exu2csr_rw_addr[4:0])
                5'd1        : csr_r_data    = mtime_ext[63:32];
`ifndef SCR1_CSR_REDUCED_CNT
                5'd0        : csr_r_data    = csr_cycle[63:32];
                5'd2        : csr_r_data    = csr_instret[63:32];
`endif // SCR1_CSR_REDUCED_CNT
                default     : begin
                    // return 0
                end
            endcase
        end

        // Machine Counters/Timers (read-write)
        {SCR1_CSR_ADDR_MHPMCOUNTER_MASK, 5'b?????}  : begin
            case (exu2csr_rw_addr[4:0])
                5'd1        : csr_r_exc     = exu2csr_r_req;
`ifndef SCR1_CSR_REDUCED_CNT
                5'd0        : csr_r_data    = csr_cycle[31:0];
                5'd2        : csr_r_data    = csr_instret[31:0];
`endif // SCR1_CSR_REDUCED_CNT
                default     : begin
                    // return 0
                end
            endcase
        end

        {SCR1_CSR_ADDR_MHPMCOUNTERH_MASK, 5'b?????} : begin
            case (exu2csr_rw_addr[4:0])
                5'd1        : csr_r_exc     = exu2csr_r_req;
`ifndef SCR1_CSR_REDUCED_CNT
                5'd0        : csr_r_data    = csr_cycle[63:32];
                5'd2        : csr_r_data    = csr_instret[63:32];
`endif // SCR1_CSR_REDUCED_CNT
                default     : begin
                    // return 0
                end
            endcase
        end

        {SCR1_CSR_ADDR_MHPMEVENT_MASK, 5'b?????}    : begin
            case (exu2csr_rw_addr[4:0])
                5'd0,
                5'd1,
                5'd2        : csr_r_exc = exu2csr_r_req;
                default     : begin
                    // return 0
                end
            endcase
        end

`ifdef SCR1_CSR_MCOUNTEN_EN
        SCR1_CSR_ADDR_MCOUNTEN      : csr_r_data    = csr_mcounten;
`endif // SCR1_CSR_MCOUNTEN_EN

`ifdef SCR1_IPIC_EN
        // IPIC registers
        SCR1_CSR_ADDR_IPIC_CISV,
        SCR1_CSR_ADDR_IPIC_CICSR,
        SCR1_CSR_ADDR_IPIC_IPR,
        SCR1_CSR_ADDR_IPIC_ISVR,
        SCR1_CSR_ADDR_IPIC_EOI,
        SCR1_CSR_ADDR_IPIC_SOI,
        SCR1_CSR_ADDR_IPIC_IDX,
        SCR1_CSR_ADDR_IPIC_ICSR     : begin
            csr_r_data      = ipic2csr_rdata;
            csr2ipic_r_req  = exu2csr_r_req;
        end
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBGC_EN
        SCR1_HDU_DBGCSR_ADDR_DCSR,
        SCR1_HDU_DBGCSR_ADDR_DPC,
        SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
        SCR1_HDU_DBGCSR_ADDR_DSCRATCH1 : begin
            // HDU register access
            csr_hdu_req = 1'b1;
            csr_r_data  = hdu2csr_rdata;
        end
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
        // TDU registers
        SCR1_CSR_ADDR_TDU_TSELECT,
        SCR1_CSR_ADDR_TDU_TDATA1,
        SCR1_CSR_ADDR_TDU_TDATA2,
        SCR1_CSR_ADDR_TDU_TINFO: begin
            csr_brkm_req    = 1'b1;
            csr_r_data      = tdu2csr_rdata;
        end
`endif // SCR1_BRKM_EN

        default     : begin
            csr_r_exc   = exu2csr_r_req;
        end
    endcase // exu2csr_rw_addr
end

assign csr2exu_r_data   = csr_r_data;

//-------------------------------------------------------------------------------
// Write CSR
//-------------------------------------------------------------------------------
always_comb begin
    case (exu2csr_w_cmd)
        SCR1_CSR_CMD_WRITE  : csr_w_data =  exu2csr_w_data;
        SCR1_CSR_CMD_SET    : csr_w_data =  exu2csr_w_data | csr_r_data;
        SCR1_CSR_CMD_CLEAR  : csr_w_data = ~exu2csr_w_data & csr_r_data;
        default             : csr_w_data = '0;
    endcase
end

always_comb begin
    csr_mstatus_up      = 1'b0;
    csr_mie_up          = 1'b0;
    csr_mscratch_up     = 1'b0;
    csr_mepc_up         = 1'b0;
    csr_mcause_up       = 1'b0;
    csr_mtval_up        = 1'b0;
    csr_mtvec_up        = 1'b0;

`ifndef SCR1_CSR_REDUCED_CNT
    csr_cycle_up        = 2'b00;
    csr_instret_up      = 2'b00;
`endif // SCR1_CSR_REDUCED_CNT

`ifdef SCR1_CSR_MCOUNTEN_EN
    csr_mcounten_up     = 1'b0;
`endif // SCR1_CSR_MCOUNTEN_EN
    csr_w_exc           = 1'b0;
`ifdef SCR1_IPIC_EN
    csr2ipic_w_req      = 1'b0;
`endif // SCR1_IPIC_EN

    if (exu2csr_w_req) begin
        casez (exu2csr_rw_addr)
            // Machine Trap Setup (read-write)
            SCR1_CSR_ADDR_MSTATUS   : csr_mstatus_up    = 1'b1;
            SCR1_CSR_ADDR_MISA      : begin end
            SCR1_CSR_ADDR_MIE       : csr_mie_up        = 1'b1;
            SCR1_CSR_ADDR_MTVEC     : csr_mtvec_up      = 1'b1;

            // Machine Trap Handling (read-write)
            SCR1_CSR_ADDR_MSCRATCH  : csr_mscratch_up   = 1'b1;
            SCR1_CSR_ADDR_MEPC      : csr_mepc_up       = 1'b1;
            SCR1_CSR_ADDR_MCAUSE    : csr_mcause_up     = 1'b1;
            SCR1_CSR_ADDR_MTVAL     : csr_mtval_up      = 1'b1;
            SCR1_CSR_ADDR_MIP       : begin end

            // Machine Counters/Timers (read-write)
            {SCR1_CSR_ADDR_MHPMCOUNTER_MASK, 5'b?????}  : begin
                case (exu2csr_rw_addr[4:0])
                    5'd1        : csr_w_exc         = 1'b1;
`ifndef SCR1_CSR_REDUCED_CNT
                    5'd0        : csr_cycle_up[0]   = 1'b1;
                    5'd2        : csr_instret_up[0] = 1'b1;
`endif // SCR1_CSR_REDUCED_CNT
                    default     : begin
                        // no exception
                    end
                endcase
            end

            {SCR1_CSR_ADDR_MHPMCOUNTERH_MASK, 5'b?????} : begin
                case (exu2csr_rw_addr[4:0])
                    5'd1        : csr_w_exc         = 1'b1;
`ifndef SCR1_CSR_REDUCED_CNT
                    5'd0        : csr_cycle_up[1]   = 1'b1;
                    5'd2        : csr_instret_up[1] = 1'b1;
`endif // SCR1_CSR_REDUCED_CNT
                    default     : begin
                        // no exception
                    end
                endcase
            end

            {SCR1_CSR_ADDR_MHPMEVENT_MASK, 5'b?????}    : begin
                case (exu2csr_rw_addr[4:0])
                    5'd0,
                    5'd1,
                    5'd2        : csr_w_exc = 1'b1;
                    default     : begin
                        // no exception
                    end
                endcase
            end

`ifdef SCR1_CSR_MCOUNTEN_EN
            SCR1_CSR_ADDR_MCOUNTEN      : csr_mcounten_up   = 1'b1;
`endif // SCR1_CSR_MCOUNTEN_EN

`ifdef SCR1_IPIC_EN
            // IPIC registers
            SCR1_CSR_ADDR_IPIC_CICSR,
            SCR1_CSR_ADDR_IPIC_IPR,
            SCR1_CSR_ADDR_IPIC_EOI,
            SCR1_CSR_ADDR_IPIC_SOI,
            SCR1_CSR_ADDR_IPIC_IDX,
            SCR1_CSR_ADDR_IPIC_ICSR     : begin
                csr2ipic_w_req  = 1'b1;
            end
            SCR1_CSR_ADDR_IPIC_CISV,
            SCR1_CSR_ADDR_IPIC_ISVR     : begin
                // no exception on write
            end
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBGC_EN
            SCR1_HDU_DBGCSR_ADDR_DCSR,
            SCR1_HDU_DBGCSR_ADDR_DPC,
            SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
            SCR1_HDU_DBGCSR_ADDR_DSCRATCH1 : begin
            end
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
            // TDU registers
            SCR1_CSR_ADDR_TDU_TSELECT,
            SCR1_CSR_ADDR_TDU_TDATA1,
            SCR1_CSR_ADDR_TDU_TDATA2,
            SCR1_CSR_ADDR_TDU_TINFO: begin
            end
`endif // SCR1_BRKM_EN

            default : begin
                csr_w_exc   = 1'b1;
            end
        endcase
    end
end

// CSR exception
assign csr2exu_rw_exc = csr_r_exc | csr_w_exc
`ifdef SCR1_DBGC_EN
                     | ((csr2hdu_req) & (hdu2csr_resp != SCR1_CSR_RESP_OK))
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
                     | ((csr2tdu_req) & (tdu2csr_resp != SCR1_CSR_RESP_OK))
`endif // SCR1_BRKM_EN
                    ;

//-------------------------------------------------------------------------------
// Events (IRQ, EXC, MRET)
//-------------------------------------------------------------------------------
assign csr2exu_mstatus_mie_up   = csr_mstatus_up | csr_mie_up | e_mret;

// Event priority
assign e_exc    = exu2csr_take_exc
`ifdef SCR1_DBGC_EN
                & ~exu_no_commit
`endif // SCR1_DBGC_EN
                ;
assign e_irq    = exu2csr_take_irq & ~exu2csr_take_exc
`ifdef SCR1_DBGC_EN
                & ~exu_no_commit
`endif // SCR1_DBGC_EN
                ;
assign e_mret   = exu2csr_mret_update
`ifdef SCR1_DBGC_EN
                & ~exu_no_commit
`endif // SCR1_DBGC_EN
                ;

// IRQ exception codes priority
always_comb begin
    case (1'b1)
        (csr_mip_meip & csr_mie_meie)   : csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_EXTERNAL);
        (csr_mip_msip & csr_mie_msie)   : csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_SOFTWARE);
        (csr_mip_mtip & csr_mie_mtie)   : csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_TIMER);
        default                         : csr_mcause_ec_new = type_scr1_exc_code_e'(SCR1_EXC_CODE_IRQ_M_EXTERNAL);
    endcase
end

// MSTATUS
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mstatus_mie     <= SCR1_CSR_MSTATUS_MIE_RST_VAL;
        csr_mstatus_mpie    <= SCR1_CSR_MSTATUS_MPIE_RST_VAL;
    end else begin
        case (1'b1)
            e_exc,
            e_irq           : begin
                csr_mstatus_mie     <= 1'b0;
                csr_mstatus_mpie    <= csr_mstatus_mie;
            end
            e_mret          : begin
                csr_mstatus_mie     <= csr_mstatus_mpie;
                csr_mstatus_mpie    <= 1'b1;
            end
            csr_mstatus_up  : begin
                csr_mstatus_mie     <= csr_w_data[SCR1_CSR_MSTATUS_MIE_OFFSET];
                csr_mstatus_mpie    <= csr_w_data[SCR1_CSR_MSTATUS_MPIE_OFFSET];
            end
            default : begin end
        endcase
    end
end

// MEPC
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mepc    <= '0;
    end else begin
        case (1'b1)
            e_exc           : begin
`ifdef SCR1_RVC_EXT
                csr_mepc    <= curr_pc[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc    <= curr_pc[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
            end
            (e_irq & ~exu2csr_mret_instr)   : begin
`ifdef SCR1_RVC_EXT
                csr_mepc    <= next_pc[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc    <= next_pc[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
            end
            csr_mepc_up     : begin
`ifdef SCR1_RVC_EXT
                csr_mepc    <= csr_w_data[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc    <= csr_w_data[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
            end
            default : begin end
        endcase
    end
end

// MCAUSE
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mcause_i    <= 1'b0;
        csr_mcause_ec   <= type_scr1_exc_code_e'(SCR1_EXC_CODE_RESET);
    end else begin
        case (1'b1)
            e_exc           : begin
                csr_mcause_i    <= 1'b0;
                csr_mcause_ec   <= exu2csr_exc_code;
            end
            e_irq           : begin
                csr_mcause_i    <= 1'b1;
                csr_mcause_ec   <= csr_mcause_ec_new;
            end
            csr_mcause_up   : begin
                csr_mcause_i    <= csr_w_data[`SCR1_XLEN-1];
                csr_mcause_ec   <= type_scr1_exc_code_e'(csr_w_data[SCR1_EXC_CODE_WIDTH_E-1:0]);
            end
            default : begin end
        endcase
    end
end

// MTVAL
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtval   <= '0;
    end else begin
        case (1'b1)
            e_exc           : begin
                csr_mtval   <= exu2csr_trap_val;
            end
            e_irq           : begin
                csr_mtval   <= '0;
            end
            csr_mtval_up    : begin
                csr_mtval   <= csr_w_data;
            end
            default : begin end
        endcase
    end
end

assign csr_mip_mtip     = timer_irq;
assign csr_mip_meip     = ext_irq;
assign csr_mip_msip     = soft_irq;
assign csr2exu_ip_ie    =   (csr_mip_meip & csr_mie_meie) |
                            (csr_mip_msip & csr_mie_msie) |
                            (csr_mip_mtip & csr_mie_mtie);
assign csr2exu_irq      = csr2exu_ip_ie & csr_mstatus_mie;

always_comb begin
`ifndef SCR1_VECT_IRQ_EN
    csr2exu_new_pc      = {csr_mtvec_base, SCR1_CSR_MTVEC_BASE_ZERO_BITS'(0)};
`else // SCR1_VECT_IRQ_EN
    if (csr_mtvec_mode == SCR1_CSR_MTVEC_MODE_VECTORED) begin
        case (1'b1)
            exu2csr_take_exc                : csr2exu_new_pc    = {csr_mtvec_base, SCR1_CSR_MTVEC_BASE_ZERO_BITS'(0)};
            (csr_mip_meip & csr_mie_meie)   : csr2exu_new_pc    = {csr_mtvec_base, SCR1_EXC_CODE_IRQ_M_EXTERNAL, 2'd0};
            (csr_mip_msip & csr_mie_msie)   : csr2exu_new_pc    = {csr_mtvec_base, SCR1_EXC_CODE_IRQ_M_SOFTWARE, 2'd0};
            (csr_mip_mtip & csr_mie_mtie)   : csr2exu_new_pc    = {csr_mtvec_base, SCR1_EXC_CODE_IRQ_M_TIMER, 2'd0};
            default                         : csr2exu_new_pc    = {csr_mtvec_base, SCR1_CSR_MTVEC_BASE_ZERO_BITS'(0)};
        endcase // 1'b1
    end else begin // direct mode
        csr2exu_new_pc  = {csr_mtvec_base, SCR1_CSR_MTVEC_BASE_ZERO_BITS'(0)};
    end
`endif // SCR1_VECT_IRQ_EN
    if (exu2csr_mret_instr & ~exu2csr_take_irq) begin
`ifdef SCR1_RVC_EXT
        csr2exu_new_pc  = {csr_mepc, 1'b0};
`else // SCR1_RVC_EXT
        csr2exu_new_pc  = {csr_mepc, 2'b00};
`endif // SCR1_RVC_EXT
    end
end

//-------------------------------------------------------------------------------
// Update CSR
//-------------------------------------------------------------------------------

// MIE
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mie_mtie <= SCR1_CSR_MIE_MTIE_RST_VAL;
        csr_mie_meie <= SCR1_CSR_MIE_MEIE_RST_VAL;
        csr_mie_msie <= SCR1_CSR_MIE_MSIE_RST_VAL;
    end else begin
        if (csr_mie_up) begin
            // CSRRW, CSRRS, CSRRC
            csr_mie_mtie <= csr_w_data[SCR1_CSR_MIE_MTIE_OFFSET];
            csr_mie_meie <= csr_w_data[SCR1_CSR_MIE_MEIE_OFFSET];
            csr_mie_msie <= csr_w_data[SCR1_CSR_MIE_MSIE_OFFSET];
        end
    end
end

// MCOUNTEN
`ifdef SCR1_CSR_MCOUNTEN_EN
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mcounten_cy <= 1'b1;
        csr_mcounten_ir <= 1'b1;
    end else begin
        if (csr_mcounten_up) begin
            csr_mcounten_cy <= csr_w_data[SCR1_CSR_MCOUNTEN_CY_OFFSET];
            csr_mcounten_ir <= csr_w_data[SCR1_CSR_MCOUNTEN_IR_OFFSET];
        end
    end
end
`endif // SCR1_CSR_MCOUNTEN_EN

// MSCRATCH
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mscratch    <= '0;
    end else begin
        if (csr_mscratch_up) begin
            // CSRRW, CSRRS, CSRRC
            csr_mscratch    <= csr_w_data;
        end
    end
end

// MTVEC
generate
    if (SCR1_CSR_MTVEC_BASE_RW_BITS == 0) begin : mtvec_base_ro
        assign csr_mtvec_base   = SCR1_CSR_MTVEC_BASE_RST_VAL;
    end else if (SCR1_CSR_MTVEC_BASE_RW_BITS == SCR1_CSR_MTVEC_BASE_VAL_BITS) begin : mtvec_base_rw
        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_mtvec_base  <= SCR1_CSR_MTVEC_BASE_RST_VAL;
            end else begin
                if (csr_mtvec_up) begin
                    csr_mtvec_base  <= csr_w_data[`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS];
                end
            end
        end
    end else begin : mtvec_base_ro_rw
        logic [(`SCR1_XLEN-1):(`SCR1_XLEN-SCR1_CSR_MTVEC_BASE_RW_BITS)]   csr_mtvec_base_reg;
        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n) begin
                csr_mtvec_base_reg <= SCR1_CSR_MTVEC_BASE_RST_VAL[(`SCR1_XLEN-1)-:SCR1_CSR_MTVEC_BASE_RW_BITS] ;
            end else begin
                if (csr_mtvec_up) begin
                    csr_mtvec_base_reg <= csr_w_data[(`SCR1_XLEN-1)-:SCR1_CSR_MTVEC_BASE_RW_BITS];
                end
            end
        end
        assign csr_mtvec_base = {csr_mtvec_base_reg, SCR1_CSR_MTVEC_BASE_RST_VAL[SCR1_CSR_MTVEC_BASE_ZERO_BITS+:SCR1_CSR_MTVEC_BASE_RO_BITS]};
    end
endgenerate

`ifdef SCR1_VECT_IRQ_EN
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtvec_mode  <= SCR1_CSR_MTVEC_MODE_DIRECT;
    end else begin
        if (csr_mtvec_up) begin
            csr_mtvec_mode  <= csr_w_data[0];
        end
    end
end
`else // SCR1_VECT_IRQ_EN
assign csr_mtvec_mode   = SCR1_CSR_MTVEC_MODE_DIRECT;
`endif // SCR1_VECT_IRQ_EN


`ifndef SCR1_CSR_REDUCED_CNT

// CYCLE
assign csr_cycle        = {csr_cycle_hi, csr_cycle_lo};
assign csr_cycle_inc_lo = 1'b1
 `ifdef SCR1_CSR_MCOUNTEN_EN
                        & csr_mcounten_cy
 `endif // SCR1_CSR_MCOUNTEN_EN
                        ;
assign csr_cycle_inc_hi = csr_cycle_inc_lo & (&csr_cycle_lo);

always_comb begin
    csr_cycle_lo_new = csr_cycle_lo;
    csr_cycle_hi_new = csr_cycle_hi;

    if (csr_cycle_inc_lo)   csr_cycle_lo_new = csr_cycle_lo + 1'b1;
    if (csr_cycle_inc_hi)   csr_cycle_hi_new = csr_cycle_hi + 1'b1;

    case (csr_cycle_up)
        2'b01   : begin
            csr_cycle_lo_new        = csr_w_data[7:0];
            csr_cycle_hi_new[31:8]  = csr_w_data[31:8];
        end
        2'b10   : begin
            csr_cycle_hi_new[63:32] = csr_w_data;
        end
        default : begin end
    endcase
end

`ifndef SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk) begin
`else // SCR1_CLKCTRL_EN
always_ff @(negedge rst_n, posedge clk_alw_on) begin
`endif // SCR1_CLKCTRL_EN
    if (~rst_n) begin
        csr_cycle_lo    <= '0;
        csr_cycle_hi    <= '0;
    end else begin
        if (csr_cycle_inc_lo | csr_cycle_up[0]) csr_cycle_lo <= csr_cycle_lo_new;
        if (csr_cycle_inc_hi | (|csr_cycle_up)) csr_cycle_hi <= csr_cycle_hi_new;
    end
end

`endif // SCR1_CSR_REDUCED_CNT

`ifndef SCR1_CSR_REDUCED_CNT

// INSTRET
assign csr_instret          = {csr_instret_hi, csr_instret_lo};
assign csr_instret_inc_lo   = instret_nexc
 `ifdef SCR1_CSR_MCOUNTEN_EN
                            & csr_mcounten_ir
 `endif // SCR1_CSR_MCOUNTEN_EN
                            ;
assign csr_instret_inc_hi   = csr_instret_inc_lo & (&csr_instret_lo);

always_comb begin
    csr_instret_lo_new = csr_instret_lo;
    csr_instret_hi_new = csr_instret_hi;

    if (csr_instret_inc_lo) csr_instret_lo_new = csr_instret_lo + 1'b1;
    if (csr_instret_inc_hi) csr_instret_hi_new = csr_instret_hi + 1'b1;

    case (csr_instret_up)
        2'b01   : begin
            csr_instret_lo_new          = csr_w_data[7:0];
            csr_instret_hi_new[31:8]    = csr_w_data[31:8];
        end
        2'b10   : begin
            csr_instret_hi_new[63:32]   = csr_w_data;
        end
        default : begin end
    endcase
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_instret_lo  <= '0;
        csr_instret_hi  <= '0;
    end else begin
        if (csr_instret_inc_lo | csr_instret_up[0]) csr_instret_lo <= csr_instret_lo_new;
        if (csr_instret_inc_hi | (|csr_instret_up)) csr_instret_hi <= csr_instret_hi_new;
    end
end

`endif // SCR1_CSR_REDUCED_CNT


`ifdef SCR1_IPIC_EN
//-------------------------------------------------------------------------------
// IPIC
//-------------------------------------------------------------------------------
assign csr2ipic_addr    = (csr2ipic_r_req | csr2ipic_w_req) ? exu2csr_rw_addr[2:0] : '0;
assign csr2ipic_wdata   = csr2ipic_w_req                    ? exu2csr_w_data       : '0;
`endif // SCR1_IPIC_EN


`ifdef SCR1_DBGC_EN
//-------------------------------------------------------------------------------
// HDU
//-------------------------------------------------------------------------------
assign csr2hdu_req      = csr_hdu_req & ((exu2csr_r_req & ~csr_r_exc) | (exu2csr_w_req & ~csr_w_exc));
assign csr2hdu_cmd      = exu2csr_w_cmd;
assign csr2hdu_addr     = exu2csr_rw_addr[SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0];
assign csr2hdu_wdata    = exu2csr_w_data;
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
//-------------------------------------------------------------------------------
// TDU
//-------------------------------------------------------------------------------
assign csr2tdu_req      = csr_brkm_req & ((exu2csr_r_req & ~csr_r_exc) | (exu2csr_w_req & ~csr_w_exc));
assign csr2tdu_cmd      = exu2csr_w_cmd;
assign csr2tdu_addr     = exu2csr_rw_addr[SCR1_CSR_ADDR_TDU_OFFS_W-1:0];
assign csr2tdu_wdata    = exu2csr_w_data;
`endif // SCR1_BRKM_EN


`ifdef SCR1_SIM_ENV
`ifndef VERILATOR
//-------------------------------------------------------------------------------
// Assertions
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_CSR_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2csr_r_req, exu2csr_w_req, exu2csr_take_irq, exu2csr_take_exc, exu2csr_mret_update
`ifndef SCR1_CSR_REDUCED_CNT
    ,instret_nexc
`endif // SCR1_CSR_REDUCED_CNT
    })
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_READ : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_r_req |-> !$isunknown({exu2csr_rw_addr, csr2exu_r_data, csr2exu_rw_exc})
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_WRITE : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_w_req |-> !$isunknown({exu2csr_rw_addr, exu2csr_w_cmd, exu2csr_w_data, csr2exu_rw_exc})
    ) else $error("CSR Error: unknown control values");

`ifdef SCR1_IPIC_EN
SCR1_SVA_CSR_XCHECK_READ_IPIC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2ipic_r_req |-> !$isunknown({csr2ipic_addr, ipic2csr_rdata})
    ) else $error("CSR Error: unknown control values");

SCR1_SVA_CSR_XCHECK_WRITE_IPIC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2ipic_w_req |-> !$isunknown({csr2ipic_addr, csr2ipic_wdata})
    ) else $error("CSR Error: unknown control values");
`endif // SCR1_IPIC_EN

// Behavior checks

SCR1_SVA_CSR_MRET : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_mret_update |=> ($stable(csr_mepc) & $stable(csr_mtval))
    ) else $error("CSR Error: MRET wrong behavior");

SCR1_SVA_CSR_MRET_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_mret_instr & e_irq) |=> ($stable(csr_mepc) & (curr_pc !=
`ifdef SCR1_RVC_EXT
                                                                    {csr_mepc, 1'b0}
`else // SCR1_RVC_EXT
                                                                    {csr_mepc, 2'b00}
`endif // SCR1_RVC_EXT
    ))
    ) else $error("CSR Error: MRET+IRQ wrong behavior");

SCR1_SVA_CSR_EXC_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_take_exc & exu2csr_take_irq) |=>
    (~csr_mstatus_mie & ~($stable(csr_mepc)) & (~csr_mcause_i) & (curr_pc=={csr_mtvec_base, SCR1_CSR_MTVEC_BASE_ZERO_BITS'(0)}))
    ) else $error("CSR Error: wrong EXC+IRQ");

SCR1_SVA_CSR_EVENTS : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({e_irq, e_exc, e_mret})
    ) else $error("CSR Error: more than one event at a time");

SCR1_SVA_CSR_RW_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2exu_rw_exc |-> (exu2csr_w_req | exu2csr_r_req)
    ) else $error("CSR Error: impossible exception");

SCR1_SVA_CSR_MSTATUS_MIE_UP : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2exu_mstatus_mie_up |=> ~csr2exu_mstatus_mie_up
    ) else $error("CSR Error: csr2exu_mstatus_mie_up can only be high for one cycle");


`ifndef SCR1_CSR_REDUCED_CNT

SCR1_SVA_CSR_CYCLE_INC : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    (~|csr_cycle_up) |=>
`ifdef SCR1_CSR_MCOUNTEN_EN
    ($past(csr_mcounten_cy) ? (csr_cycle == $past(csr_cycle + 1'b1)) : $stable(csr_cycle))
`else //SCR1_CSR_MCOUNTEN_EN
    (csr_cycle == $past(csr_cycle + 1'b1))
`endif // SCR1_CSR_MCOUNTEN_EN
    ) else $error("CSR Error: CYCLE increment wrong behavior");

SCR1_SVA_CSR_INSTRET_INC : assert property (
    @(negedge clk) disable iff (~rst_n)
    (instret_nexc & ~|csr_instret_up) |=>
`ifdef SCR1_CSR_MCOUNTEN_EN
    ($past(csr_mcounten_ir) ? (csr_instret == $past(csr_instret + 1'b1)) : $stable(csr_instret))
`else //SCR1_CSR_MCOUNTEN_EN
    (csr_instret == $past(csr_instret + 1'b1))
`endif // SCR1_CSR_MCOUNTEN_EN
    ) else $error("CSR Error: INSTRET increment wrong behavior");

SCR1_SVA_CSR_CYCLE_INSTRET_UP : assert property (
    @(negedge clk) disable iff (~rst_n)
    ~(&csr_instret_up | &csr_cycle_up)
    ) else $error("CSR Error: INSTRET/CYCLE up illegal value");

`endif // SCR1_CSR_REDUCED_CNT

`endif // VERILATOR
`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_csr

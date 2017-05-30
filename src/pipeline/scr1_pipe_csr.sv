/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_pipe_csr.sv>
/// @brief      Control Status Registers
///

`include "scr1_arch_description.svh"
`include "scr1_csr_map.svh"
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBGC_EN
`include "scr1_dbgc.svh"
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
 `include "scr1_brkm.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_csr (
    // Common
    input   logic                                       rst_n,
    input   logic                                       clk,
`ifdef SCR1_CLKCTRL_EN
    input   logic                                       clk_alw_on,
`endif // SCR1_CLKCTRL_EN
    input   logic                                       rtc_clk,

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
    input   logic                                       exu2csr_take_eret,      // ERET instruction
    input   type_scr1_exc_code_e                        exu2csr_exc_code,       // Exception code (see scr1_arch_types.svh)
    input   logic [`SCR1_XLEN-1:0]                      exu2csr_exc_badaddr,    // Exception bad address
    output  logic [`SCR1_XLEN-1:0]                      csr2exu_new_pc,         // Exception/IRQ/ERET new PC
    output  logic                                       csr2exu_irq,            // IRQ request
    output  logic                                       csr2exu_irq_pen,        // IRQ pending

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

    // External interupt interface
    input   logic                                       ext_irq,                // External interupt request

`ifdef SCR1_DBGC_EN
    // CSR <-> DBGA interface
    input   logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    dbga2csr_ddr,           // DBGA read data
    output  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    csr2dbga_ddr,           // DBGA write data
    output  logic                                       csr2dbga_ddr_we,        // DBGA write request
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
    // CSR <-> BRKM interface
    output  logic                                       csr2brkm_req,           // Request to BRKM
    output  type_scr1_csr_cmd_sel_e                     csr2brkm_cmd,           // BRKM command
    output  logic [SCR1_BRKM_PKG_CSR_OFFS_WIDTH-1:0]    csr2brkm_addr,          // BRKM address
    output  logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr2brkm_wdata,         // BRKM write data
    input   logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    brkm2csr_rdata,         // BRKM read data
    input   type_scr1_csr_resp_e                        brkm2csr_resp,          // BRKM response
`endif // SCR1_BRKM_EN

    // MHARTID fuse
    input   logic [`SCR1_XLEN-1:0]                      fuse_mhartid            // MHARTID fuse
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Registers
logic                                   csr_mstatus_ie0;    // MSTATUS: Global interupt enable
logic                                   csr_mstatus_ie1;    // MSTATUS: Interupt enable bit for nested trap level 1
logic                                   csr_mie_mtie;       // MIE: Machine timer interupt enable
logic                                   csr_mie_meie;       // MIE: Machine external interupt enable
logic [`SCR1_XLEN-1:0]                  csr_mtimecmp;       // MTIMECMP
logic [SCR1_CSR_MTIMECLKSET_WIDTH-1:0]  csr_mtimeclkset;    // MTIMECLKSET
logic [`SCR1_XLEN-1:0]                  csr_mscratch;       // MSCRATCH
`ifdef SCR1_RVC_EXT
logic [`SCR1_XLEN-1:1]                  csr_mepc;           // MEPC (RVC)
`else // ~SCR1_RVC_EXT
logic [`SCR1_XLEN-1:2]                  csr_mepc;           // MEPC
`endif // ~SCR1_RVC_EXT
logic                                   csr_mcause_i;       // MCAUSE: Interupt
logic [SCR1_CSR_MCAUSE_EC_WIDTH-1:0]    csr_mcause_ec;      // MCAUSE: Exception code
logic [`SCR1_XLEN-1:0]                  csr_mbadaddr;       // MBADADDR
logic                                   csr_mip_mtip;       // MIP: Machine timer interupt pending
logic                                   csr_mip_meip;       // MIP: Machine external interupt pending
logic [SCR1_CSR_COUNTERS_WIDTH-1:0]     csr_time;           // TIME
`ifndef SCR1_CSR_REDUCED_CNT
logic [SCR1_CSR_COUNTERS_WIDTH-1:0]     csr_instret;        // INSTRET
logic [SCR1_CSR_COUNTERS_WIDTH-1:0]     csr_cycle;          // CYCLE
`endif // ~SCR1_CSR_REDUCED_CNT

// Read signals
logic [`SCR1_XLEN-1:0]                  csr_r_data;
logic                                   csr_r_exc;

// Write signals
logic                                   csr_mstatus_up;
logic                                   csr_mie_up;
logic                                   csr_mtimecmp_up;
logic                                   csr_mtimeclkset_up;
logic                                   csr_mscratch_up;
logic                                   csr_mepc_up;
logic                                   csr_time_up;
`ifndef SCR1_CSR_REDUCED_CNT
logic                                   csr_timeh_up;
`endif // SCR1_CSR_REDUCED_CNT
logic [`SCR1_XLEN-1:0]                  csr_w_data;
logic                                   csr_w_exc;

// Exception and interrupt signals
logic                                   time_irq;
logic                                   time_irq_en;
logic                                   csr_mtimecmp_init;
logic                                   ext_irq_en;
logic                                   csr_mstatus_ie0_new;    // IE0 after write to mstatus
logic                                   csr_mie_mtie_new;       // MTIE after write to MIE
logic                                   csr_mie_meie_new;       // MEIE after write to MIE

// Events
logic                                   e_exc;
logic                                   e_irq;
logic                                   e_eret;
logic                                   e_eret_irq;

// Update signals for time
logic                                   rtc_internal;
logic [3:0]                             rtc_sync;
logic                                   rtc_ext_pulse;
logic [SCR1_CSR_TIMECLK_CNT_WIDTH-1:0]  timeclk_cnt;
logic                                   timeclk_cnt_en;
logic                                   time_posedge;

`ifdef SCR1_BRKM_EN
logic                                   csr_brkm_req;
`endif // SCR1_BRKM_EN

//-------------------------------------------------------------------------------
// Read CSR
//-------------------------------------------------------------------------------
always_comb begin
    csr_r_data      = '0;
    csr_r_exc       = 1'b0;
`ifdef SCR1_IPIC_EN
    csr2ipic_r_req  = 1'b0;
`endif // SCR1_IPIC_EN
`ifdef SCR1_BRKM_EN
    csr_brkm_req   = 1'b0;
`endif // SCR1_BRKM_EN
    case (exu2csr_rw_addr)
        // Machine Information Registers (MRO)
        SCR1_CSR_ADDR_MCPUID   : begin
            csr_r_data  = `SCR1_CSR_MCPUID;
        end
        SCR1_CSR_ADDR_MIMPID   : begin
            csr_r_data  = SCR1_CSR_MIMPID;
        end
        SCR1_CSR_ADDR_MHARTID  : begin
            csr_r_data  = fuse_mhartid;
        end
        SCR1_CSR_ADDR_MRTLID   : begin
            csr_r_data  = SCR1_CSR_MRTLID;
        end

        // Machine Trap Setup (MRW)
        SCR1_CSR_ADDR_MSTATUS  : begin
            csr_r_data  = {'0, SCR1_CSR_MSTATUS_PRV_VAL, csr_mstatus_ie1, SCR1_CSR_MSTATUS_PRV_VAL, csr_mstatus_ie0};
        end
        SCR1_CSR_ADDR_MTVEC    : begin
            csr_r_data  = SCR1_CSR_MTVEC;
        end
        SCR1_CSR_ADDR_MTDELEG  : begin
            csr_r_data  = '0;
        end
        SCR1_CSR_ADDR_MIE      : begin
            csr_r_data  = {'0, csr_mie_meie, 3'b0, csr_mie_mtie, 7'b0};
        end
        SCR1_CSR_ADDR_MTIMECMP : begin
            csr_r_data  = csr_mtimecmp;
        end

        // Machine timers and counters (MRW)
        SCR1_CSR_ADDR_MTIME    : begin
            csr_r_data  = csr_time[31:0];
        end
`ifndef SCR1_CSR_REDUCED_CNT
        SCR1_CSR_ADDR_MTIMEH   : begin
            csr_r_data  = csr_time[63:32];
        end
`endif // SCR1_CSR_REDUCED_CNT
        SCR1_CSR_ADDR_MTIMECLKSET : begin
            csr_r_data  = {'0, csr_mtimeclkset};
        end

        // Machine Trap Handling (MRW)
        SCR1_CSR_ADDR_MSCRATCH : begin
            csr_r_data  = csr_mscratch;
        end
        SCR1_CSR_ADDR_MEPC     : begin
`ifdef SCR1_RVC_EXT
            csr_r_data  = {csr_mepc, 1'b0};
`else // ~SCR1_RVC_EXT
            csr_r_data  = {csr_mepc, 2'b00};
`endif // ~SCR1_RVC_EXT
        end
        SCR1_CSR_ADDR_MCAUSE   : begin
            csr_r_data  = {csr_mcause_i, SCR1_CSR_MCAUSE_GAP_WIDTH'(1'b0), csr_mcause_ec};
        end
        SCR1_CSR_ADDR_MBADADDR : begin
            csr_r_data  = csr_mbadaddr;
        end
        SCR1_CSR_ADDR_MIP      : begin
            csr_r_data  = {'0, csr_mip_meip, 3'b0, csr_mip_mtip, 7'b0};
        end

        // User Countes/Timers (RO)
        SCR1_CSR_ADDR_TIME     : begin
            csr_r_data  = csr_time[`SCR1_XLEN-1:0];
        end
`ifndef SCR1_CSR_REDUCED_CNT
        SCR1_CSR_ADDR_TIMEH    : begin
            csr_r_data  = csr_time[SCR1_CSR_COUNTERS_WIDTH-1:`SCR1_XLEN];
        end
        SCR1_CSR_ADDR_INSTRET  : begin
            csr_r_data  = csr_instret[`SCR1_XLEN-1:0];
        end
        SCR1_CSR_ADDR_INSTRETH : begin
            csr_r_data  = csr_instret[SCR1_CSR_COUNTERS_WIDTH-1:`SCR1_XLEN];
        end
        SCR1_CSR_ADDR_CYCLE    : begin
            csr_r_data  = csr_cycle[`SCR1_XLEN-1:0];
        end
        SCR1_CSR_ADDR_CYCLEH   : begin
            csr_r_data  = csr_cycle[SCR1_CSR_COUNTERS_WIDTH-1:`SCR1_XLEN];
        end
`endif // SCR1_CSR_REDUCED_CNT

`ifdef SCR1_IPIC_EN
        // IPIC
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
        // Debug Data Register (DDR)
        SCR1_CSR_ADDR_DBGC_SCRATCH : begin
            csr_r_data      = dbga2csr_ddr;
        end
`endif // SCR1_DBGC_EN

        // BRKM
`ifdef SCR1_BRKM_EN
        SCR1_BRKM_PKG_CSR_ADDR_BPSELECT,
        SCR1_BRKM_PKG_CSR_ADDR_BPCONTROL,
        SCR1_BRKM_PKG_CSR_ADDR_BPLOADDR,
        SCR1_BRKM_PKG_CSR_ADDR_BPHIADDR,
        SCR1_BRKM_PKG_CSR_ADDR_BPLODATA,
        SCR1_BRKM_PKG_CSR_ADDR_BPHIDATA,
        SCR1_BRKM_PKG_CSR_ADDR_BPCTRLEXT,
        SCR1_BRKM_PKG_CSR_ADDR_BRKMCTRL : begin
            csr_brkm_req    = 1'b1;
            csr_r_data      = brkm2csr_rdata;
        end
`endif // SCR1_BRKM_EN

        default : begin
            if (exu2csr_r_req) begin
                csr_r_exc   = 1'b1;
            end
        end
    endcase
end

assign csr2exu_r_data    = csr_r_data;

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
    csr_mtimecmp_up     = 1'b0;
    csr_mtimeclkset_up  = 1'b0;
    csr_mscratch_up     = 1'b0;
    csr_mepc_up         = 1'b0;
    csr_time_up         = 1'b0;
`ifndef SCR1_CSR_REDUCED_CNT
    csr_timeh_up        = 1'b0;
`endif // SCR1_CSR_REDUCED_CNT
    csr_w_exc           = 1'b0;
`ifdef SCR1_IPIC_EN
    csr2ipic_w_req      = 1'b0;
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBGC_EN
    csr2dbga_ddr_we     = 1'b0;
    csr2dbga_ddr        = '0;
`endif // SCR1_DBGC_EN

    if (exu2csr_w_req) begin
        case (exu2csr_rw_addr)
            // Machine Trap Setup (MRW)
            SCR1_CSR_ADDR_MSTATUS : begin
                // Partly RO
                csr_mstatus_up  = 1'b1;
            end
            SCR1_CSR_ADDR_MTVEC : begin
                // RO
            end
            SCR1_CSR_ADDR_MTDELEG : begin
                // RZ
            end
            SCR1_CSR_ADDR_MIE : begin
                // Partly RO
                csr_mie_up      = 1'b1;
            end
            SCR1_CSR_ADDR_MTIMECMP : begin
                csr_mtimecmp_up = 1'b1;
            end

            // Machine timers and counters (MRW)
            SCR1_CSR_ADDR_MTIME : begin
                csr_time_up     = 1'b1;
            end
`ifndef SCR1_CSR_REDUCED_CNT
            SCR1_CSR_ADDR_MTIMEH : begin
                csr_timeh_up    = 1'b1;
            end
`endif // SCR1_CSR_REDUCED_CNT
            SCR1_CSR_ADDR_MTIMECLKSET : begin
                csr_mtimeclkset_up  = 1'b1;
            end

            // Machine Trap Handling (MRW)
            SCR1_CSR_ADDR_MSCRATCH : begin
                csr_mscratch_up = 1'b1;
            end
            SCR1_CSR_ADDR_MEPC     : begin
                csr_mepc_up     = 1'b1;
            end
            SCR1_CSR_ADDR_MCAUSE   : begin
                // RO
            end
            SCR1_CSR_ADDR_MBADADDR : begin
                // RO
            end
            SCR1_CSR_ADDR_MIP      : begin
                // RO
            end

`ifdef SCR1_IPIC_EN
            // IPIC
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
            // Debug Data Register (DDR)
            SCR1_CSR_ADDR_DBGC_SCRATCH : begin
                csr2dbga_ddr_we = 1'b1;
                csr2dbga_ddr    = exu2csr_w_data;
            end
`endif // SCR1_DBGC_EN

            // BRKM
`ifdef SCR1_BRKM_EN
            SCR1_BRKM_PKG_CSR_ADDR_BPSELECT,
            SCR1_BRKM_PKG_CSR_ADDR_BPCONTROL,
            SCR1_BRKM_PKG_CSR_ADDR_BPLOADDR,
            SCR1_BRKM_PKG_CSR_ADDR_BPHIADDR,
            SCR1_BRKM_PKG_CSR_ADDR_BPLODATA,
            SCR1_BRKM_PKG_CSR_ADDR_BPHIDATA,
            SCR1_BRKM_PKG_CSR_ADDR_BPCTRLEXT,
            SCR1_BRKM_PKG_CSR_ADDR_BRKMCTRL : begin
                // Empty slot - needed for proper csr_w_exc forming
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
`ifdef SCR1_BRKM_EN
                     | ((csr2brkm_req) & (brkm2csr_resp != SCR1_CSR_RESP_OK))
`endif // SCR1_BRKM_EN
                    ;

//-------------------------------------------------------------------------------
// Events (IRQ, EXC, ERET)
//-------------------------------------------------------------------------------
assign e_exc        = exu2csr_take_exc;
assign e_eret       = exu2csr_take_eret & ~(exu2csr_take_irq & csr_mstatus_ie1);
assign e_eret_irq   = exu2csr_take_eret & exu2csr_take_irq & csr_mstatus_ie1;       // special case
assign e_irq        = exu2csr_take_irq & ~exu2csr_take_exc & ~exu2csr_take_eret;


always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mstatus_ie0 <= SCR1_CSR_MSTATUS_IE0_RST_VAL;
        csr_mstatus_ie1 <= SCR1_CSR_MSTATUS_IE1_RST_VAL;
        csr_mepc        <= '0;
        csr_mcause_i    <= 1'b0;
        csr_mcause_ec   <= '0;
        csr_mbadaddr    <= '0;
    end else begin
        case (1'b1)
            e_exc           : begin
                // EXC trap
                csr_mstatus_ie0 <= SCR1_CSR_MSTATUS_IE_PUSH_VAL;
                csr_mstatus_ie1 <= csr_mstatus_ie0;
`ifdef SCR1_RVC_EXT
                csr_mepc        <= curr_pc[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc        <= curr_pc[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
                csr_mcause_i    <= 1'b0;
                csr_mcause_ec   <= exu2csr_exc_code;
                if ((exu2csr_exc_code == SCR1_CSR_MCAUSE_IADDR_MSALL)   |
                    (exu2csr_exc_code == SCR1_CSR_MCAUSE_IACC_FAULT)    |
                    (exu2csr_exc_code == SCR1_CSR_MCAUSE_LADDR_MSALL)   |
                    (exu2csr_exc_code == SCR1_CSR_MCAUSE_LACC_FAULT)    |
                    (exu2csr_exc_code == SCR1_CSR_MCAUSE_SADDR_MSALL)   |
                    (exu2csr_exc_code == SCR1_CSR_MCAUSE_SACC_FAULT)) begin
                    csr_mbadaddr    <= exu2csr_exc_badaddr;
                end
            end

            e_irq           : begin
                // IRQ trap
                csr_mstatus_ie0 <= SCR1_CSR_MSTATUS_IE_PUSH_VAL;
                csr_mstatus_ie1 <= csr_mstatus_ie0_new;
`ifdef SCR1_RVC_EXT
                csr_mepc        <= next_pc[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc        <= next_pc[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
                csr_mcause_i    <= 1'b1;
                csr_mcause_ec   <= (csr_mip_meip) ? SCR1_CSR_MCAUSE_MEIRQ : SCR1_CSR_MCAUSE_MTIRQ;
            end

            e_eret          : begin
                // ERET
                csr_mstatus_ie0 <= csr_mstatus_ie1;
                csr_mstatus_ie1 <= SCR1_CSR_MSTATUS_IE_POP_VAL;
            end

            e_eret_irq      : begin
                // ERET + IRQ + IE1==1
                csr_mstatus_ie0 <= SCR1_CSR_MSTATUS_IE_PUSH_VAL;
                csr_mcause_i    <= 1'b1;
                csr_mcause_ec   <= (csr_mip_meip) ? SCR1_CSR_MCAUSE_MEIRQ : SCR1_CSR_MCAUSE_MTIRQ;
            end

            csr_mstatus_up  : begin
                // CSRRW, CSRRS, CSRRC
                csr_mstatus_ie0 <= csr_w_data[SCR1_CSR_MSTATUS_IE0_OFFSET];
                csr_mstatus_ie1 <= csr_w_data[SCR1_CSR_MSTATUS_IE1_OFFSET];
            end

            csr_mepc_up     : begin
                // CSRRW, CSRRS, CSRRC
`ifdef SCR1_RVC_EXT
                csr_mepc        <= csr_w_data[`SCR1_XLEN-1:1];
`else // SCR1_RVC_EXT
                csr_mepc        <= csr_w_data[`SCR1_XLEN-1:2];
`endif // SCR1_RVC_EXT
            end
        endcase // 1'b1
    end
end

always_comb begin
    csr2exu_new_pc       = SCR1_MTRAP_VECTOR;
    if (e_eret) begin
`ifdef SCR1_RVC_EXT
        csr2exu_new_pc   = {csr_mepc, 1'b0};
`else // SCR1_RVC_EXT
        csr2exu_new_pc   = {csr_mepc, 2'b00};
`endif // SCR1_RVC_EXT
    end
end

//-------------------------------------------------------------------------------
// Update CSR
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mie_mtie <= SCR1_CSR_MIE_MTIE_RST_VAL;
        csr_mie_meie <= SCR1_CSR_MIE_MEIE_RST_VAL;
    end else begin
        if (csr_mie_up) begin
            // CSRRW, CSRRS, CSRRC
            csr_mie_mtie <= csr_w_data[SCR1_CSR_MIE_MTIE_OFFSET];
            csr_mie_meie <= csr_w_data[SCR1_CSR_MIE_MEIE_OFFSET];
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtimecmp        <= '0;
        csr_mtimecmp_init   <= 1'b0;
    end else begin
        if (csr_mtimecmp_up) begin
            // CSRRW, CSRRS, CSRRC
            csr_mtimecmp        <= csr_w_data;
            csr_mtimecmp_init   <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_mtimeclkset <= {'0, 1'b1, SCR1_CSR_MTIMECLKSET_RST_VAL};
    end else begin
        if (csr_mtimeclkset_up) begin
            // CSRRW, CSRRS, CSRRC
            csr_mtimeclkset <= csr_w_data[SCR1_CSR_MTIMECLKSET_WIDTH-1:0];
        end
    end
end

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

assign csr_mstatus_ie0_new  = csr_mstatus_up    ? csr_w_data[SCR1_CSR_MSTATUS_IE0_OFFSET]   : csr_mstatus_ie0;
assign csr_mie_meie_new     = csr_mie_up        ? csr_w_data[SCR1_CSR_MIE_MEIE_OFFSET]      : csr_mie_meie;
assign csr_mie_mtie_new     = csr_mie_up        ? csr_w_data[SCR1_CSR_MIE_MTIE_OFFSET]      : csr_mie_mtie;

assign time_irq     = (csr_mtimecmp == csr_time[`SCR1_XLEN-1:0]) & csr_mtimecmp_init;
assign time_irq_en  = csr_mie_mtie_new & csr_mstatus_ie0_new;
assign ext_irq_en   = csr_mie_meie_new & csr_mstatus_ie0_new;

always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        csr_mip_mtip <= 1'b0;
    end else begin
        if (csr_mtimecmp_up) begin
            // Clear timer interrupt pending
            csr_mip_mtip    <= 1'b0;
        end else if (time_irq) begin
            // Set timer interrupt pending
            csr_mip_mtip    <= 1'b1;
        end
    end
end

assign csr_mip_meip     = ext_irq;

assign csr2exu_irq_pen  = csr_mip_meip | csr_mip_mtip;
assign csr2exu_irq      = (csr_mip_meip & ext_irq_en) | (csr_mip_mtip & time_irq_en);

assign rtc_internal     = csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_RTC_INT_OFFSET];

always_ff @(negedge rst_n, posedge rtc_clk) begin
    if (~rst_n) begin
        rtc_sync[0] <= 1'b0;
    end else begin
        if (~rtc_internal) begin
            rtc_sync[0] <= ~rtc_sync[0];
        end
    end
end

always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        rtc_sync[3:1]   <= '0;
    end else begin
        if (~rtc_internal) begin
            rtc_sync[3:1]   <= rtc_sync[2:0];
        end
    end
end

assign rtc_ext_pulse    = rtc_sync[3] ^ rtc_sync[2];
assign timeclk_cnt_en   = rtc_internal ? 1'b1 : rtc_ext_pulse;

always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        timeclk_cnt     <= '0;
    end else begin
        if (csr_mtimeclkset_up) begin
            timeclk_cnt     <= csr_w_data[SCR1_CSR_TIMECLK_CNT_WIDTH-1:0];
        end else begin
            if (time_posedge) begin
                timeclk_cnt     <= csr_mtimeclkset[SCR1_CSR_TIMECLK_CNT_WIDTH-1:0];
            end else begin
                if (timeclk_cnt_en) begin
                    timeclk_cnt     <= timeclk_cnt - 1'b1;
                end
            end
        end
    end
end

assign time_posedge     = (timeclk_cnt_en & ~|timeclk_cnt[SCR1_CSR_TIMECLK_CNT_WIDTH-1:1]);

always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        csr_time    <= '0;
    end else begin
        if (csr_time_up) begin
            csr_time[`SCR1_XLEN-1:0]  <= csr_w_data;
        end else begin
`ifndef SCR1_CSR_REDUCED_CNT
            if (csr_timeh_up) begin
                csr_time[SCR1_CSR_COUNTERS_WIDTH-1:`SCR1_XLEN] <= csr_w_data;
            end else begin
                if (time_posedge
 `ifdef SCR1_CSR_CNT_FLAG
                    & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_TIME_STOP_OFFSET]
 `endif // SCR1_CSR_CNT_FLAG
                ) begin
                    csr_time    <= csr_time + 1'b1;
                end
            end
`else // SCR1_CSR_REDUCED_CNT
            if (time_posedge
 `ifdef SCR1_CSR_CNT_FLAG
                & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_TIME_STOP_OFFSET]
 `endif // SCR1_CSR_CNT_FLAG
            ) begin
                csr_time    <= csr_time + 1'b1;
            end
`endif // SCR1_CSR_REDUCED_CNT
        end
    end
end

`ifndef SCR1_CSR_REDUCED_CNT
always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        csr_cycle       <= '0;
    end else begin
 `ifdef SCR1_CSR_CNT_FLAG
        if (~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_CYCLE_STOP_OFFSET]) begin
            csr_cycle   <= csr_cycle + 1'b1;
        end
 `else // ~SCR1_CSR_CNT_FLAG
        csr_cycle   <= csr_cycle + 1'b1;
 `endif // ~SCR1_CSR_CNT_FLAG
    end
end
`endif // SCR1_CSR_REDUCED_CNT

`ifndef SCR1_CSR_REDUCED_CNT
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_instret <= '0;
    end else begin
        if (instret_nexc
 `ifdef SCR1_CSR_CNT_FLAG
            & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_INSTRET_STOP_OFFSET]
 `endif // SCR1_CSR_CNT_FLAG
        ) begin
            csr_instret <= csr_instret + 1'b1;
        end
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

`ifdef SCR1_BRKM_EN
//-------------------------------------------------------------------------------
// BRKM
//-------------------------------------------------------------------------------
assign csr2brkm_req     = csr_brkm_req & ((exu2csr_r_req & ~csr_r_exc) | (exu2csr_w_req & ~csr_w_exc));
assign csr2brkm_cmd     = exu2csr_w_cmd;
assign csr2brkm_addr    = exu2csr_rw_addr[SCR1_BRKM_PKG_CSR_OFFS_WIDTH-1:0];
assign csr2brkm_wdata   = exu2csr_w_data;
`endif // SCR1_BRKM_EN


`ifdef SCR1_SYN_OFF_EN
// pragma synthesis_off
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_CSR_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2csr_r_req, exu2csr_w_req, exu2csr_take_irq, exu2csr_take_exc, exu2csr_take_eret
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

SCR1_SVA_CSR_ERET : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_take_eret |=> ($stable(csr_mepc) & $stable(csr_mbadaddr))
    ) else $error("CSR Error: ERET wrong behavior");

SCR1_SVA_CSR_ERET_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_take_eret & exu2csr_take_irq & csr_mstatus_ie1) |=>
    (~csr_mstatus_ie0 & $stable(csr_mepc) & (csr_mcause_i==1'b1) & (curr_pc==SCR1_MTRAP_VECTOR))
    ) else $error("CSR Error: wrong ERET+IRQ when IE1==1");

SCR1_COV_CSR_ERET_IRQ_IE1 : cover property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_take_eret & exu2csr_take_irq & csr_mstatus_ie1)
);

SCR1_SVA_CSR_EXC_IRQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2csr_take_exc & exu2csr_take_irq) |=>
    (~csr_mstatus_ie0 & ~($stable(csr_mepc)) & (~csr_mcause_i) & (curr_pc==SCR1_MTRAP_VECTOR))
    ) else $error("CSR Error: wrong EXC+IRQ");

SCR1_SVA_CSR_EVENTS : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({e_irq, e_exc, e_eret, e_eret_irq})
    ) else $error("CSR Error: more than one event at a time");

SCR1_SVA_CSR_RW_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2exu_rw_exc |-> (exu2csr_w_req | exu2csr_r_req)
    ) else $error("CSR Error: impossible exception");

SCR1_SVA_CSR_TIME_INC : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    (time_posedge & ~csr_time_up
`ifndef SCR1_CSR_REDUCED_CNT
        & ~csr_timeh_up
`endif // SCR1_CSR_REDUCED_CNT
`ifdef SCR1_CSR_CNT_FLAG
        & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_TIME_STOP_OFFSET]
`endif // SCR1_CSR_CNT_FLAG
    ) |=> (csr_time == $past(csr_time + 1'b1))
    ) else $error("CSR Error: TIME increment wrong behavior");

SCR1_SVA_CSR_TIME_STOP : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    ((~time_posedge
`ifdef SCR1_CSR_CNT_FLAG
        | csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_TIME_STOP_OFFSET]
`endif // SCR1_CSR_CNT_FLAG
    ) & ~csr_time_up
`ifndef SCR1_CSR_REDUCED_CNT
    & ~csr_timeh_up
`endif // SCR1_CSR_REDUCED_CNT
    ) |=> $stable(csr_time)
    ) else $error("CSR Error: TIME stop wrong behavior");

`ifndef SCR1_CSR_REDUCED_CNT

SCR1_SVA_CSR_CYCLE_INC : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    (1'b1
`ifdef SCR1_CSR_CNT_FLAG
        & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_CYCLE_STOP_OFFSET]
`endif // SCR1_CSR_CNT_FLAG
    ) |=> (csr_cycle == $past(csr_cycle + 1'b1))
    ) else $error("CSR Error: CYCLE increment wrong behavior");

`ifdef SCR1_CSR_CNT_FLAG
SCR1_SVA_CSR_CYCLE_STOP : assert property (
    @(
`ifndef SCR1_CLKCTRL_EN
negedge clk
`else // SCR1_CLKCTRL_EN
negedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
    ) disable iff (~rst_n)
    (csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_CYCLE_STOP_OFFSET])
    |=>  $stable(csr_cycle)
    ) else $error("CSR Error: CYCLE stop wrong behavior");
`endif // SCR1_CSR_CNT_FLAG

SCR1_SVA_CSR_INSTRET_INC : assert property (
    @(negedge clk) disable iff (~rst_n)
    (instret_nexc
`ifdef SCR1_CSR_CNT_FLAG
        & ~csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_INSTRET_STOP_OFFSET]
`endif // SCR1_CSR_CNT_FLAG
    ) |=> (csr_instret == $past(csr_instret + 1'b1))
    ) else $error("CSR Error: INSTRET increment wrong behavior");

SCR1_SVA_CSR_INSTRET_STOP : assert property (
    @(negedge clk) disable iff (~rst_n)
    (~instret_nexc
`ifdef SCR1_CSR_CNT_FLAG
    | csr_mtimeclkset[SCR1_CSR_MTIMECLKSET_INSTRET_STOP_OFFSET]
`endif // SCR1_CSR_CNT_FLAG
    ) |=>  $stable(csr_instret)
    ) else $error("CSR Error: INSTRET stop wrong behavior");

`endif // SCR1_CSR_REDUCED_CNT

// pragma synthesis_on
`endif // SCR1_SYN_OFF_EN

endmodule : scr1_pipe_csr

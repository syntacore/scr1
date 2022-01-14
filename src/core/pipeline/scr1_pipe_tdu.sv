/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_pipe_tdu.sv>
/// @brief      Trigger Debug Unit (TDU)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Provides read/write interface for TDU CSRs
 // - Provides triggers functionality:
 //   - Supports triggers either in both Debug and M modes or in Debug mode only
 //   - Supports virtual address matching (load, store, exec) triggers
 //   - Supports instruction count triggers
 //   - Supports the following actions on trigger firing:
 //     - Breakpoint exception raising
 //     - Debug Mode entering
 //   - Supports triggers chaining
 //
 // Structure:
 // - CSR read/write i/f
 // - TDU CSRs:
 //   - TSELECT
 //   - TDATA1/MCONTROL/ICOUNT
 //   - TDATA2
 //   - TINFO
 // - TDU <-> EXU i/f
 // - TDU <-> LSU i/f
 // - TDU <-> HDU i/f
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"

`ifdef SCR1_TDU_EN
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_tdu.svh"

module scr1_pipe_tdu (
    // Common signals
    input  logic                                            rst_n,                      // TDU reset
    input  logic                                            clk,                        // TDU clock
    input  logic                                            clk_en,                     // TDU clock enable
    input  logic                                            tdu_dsbl_i,                 // TDU Disable

    // TDU <-> CSR interface
    input  logic                                            csr2tdu_req_i,              // CSR-TDU i/f request
    input  type_scr1_csr_cmd_sel_e                          csr2tdu_cmd_i,              // CSR-TDU i/f command
    input  logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]             csr2tdu_addr_i,             // CSR-TDU i/f address
    input  logic [SCR1_TDU_DATA_W-1:0]                      csr2tdu_wdata_i,            // CSR-TDU i/f write data
    output logic [SCR1_TDU_DATA_W-1:0]                      tdu2csr_rdata_o,            // CSR-TDU i/f read data
    output type_scr1_csr_resp_e                             tdu2csr_resp_o,             // CSR-TDU i/f response

    // TDU <-> EXU interface
    input  type_scr1_brkm_instr_mon_s                       exu2tdu_imon_i,             // Instruction stream monitoring
    output logic [SCR1_TDU_ALLTRIG_NUM-1 : 0]               tdu2exu_ibrkpt_match_o,     // Instruction BP match
    output logic                                            tdu2exu_ibrkpt_exc_req_o,   // Instruction BP exception request
    input  logic [SCR1_TDU_ALLTRIG_NUM-1 : 0]               exu2tdu_bp_retire_i,        // Map of BPs being retired

    // TDU <-> LSU interface
`ifndef SCR1_TDU_EN
    output logic                                            tdu2lsu_brk_en_o,           // TDU-LSU Breakpoint enable
`endif // SCR1_TDU_EN
    output logic                                            tdu2lsu_ibrkpt_exc_req_o,   // TDU-LSU Instruction BP exception request
    input  type_scr1_brkm_lsu_mon_s                         lsu2tdu_dmon_i,             // TDU-LSU Data address stream monitoring
    output logic [SCR1_TDU_MTRIG_NUM-1 : 0]                 tdu2lsu_dbrkpt_match_o,     // TDU-LSU Data BP match
    output logic                                            tdu2lsu_dbrkpt_exc_req_o,   // TDU-LSU Data BP exception request

    // TDU <-> HDU interface
    output logic                                            tdu2hdu_dmode_req_o         // Debug Mode redirection request
);

//------------------------------------------------------------------------------
// Local parameters declaration
//------------------------------------------------------------------------------

localparam int unsigned MTRIG_NUM   = SCR1_TDU_MTRIG_NUM;
localparam int unsigned ALLTRIG_NUM = SCR1_TDU_ALLTRIG_NUM;
localparam int unsigned ALLTRIG_W   = $clog2(ALLTRIG_NUM+1);

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// TDU CSRs read/write i/f signals
//------------------------------------------------------------------------------

// Write signals
logic                                           csr_wr_req;
logic [SCR1_TDU_DATA_W-1:0]                     csr_wr_data;

// Register select
logic                                           csr_addr_tselect;
logic [MTRIG_NUM-1:0]                           csr_addr_mcontrol;
logic [MTRIG_NUM-1:0]                           csr_addr_tdata2;
`ifdef SCR1_TDU_ICOUNT_EN
logic                                           csr_addr_icount;
`endif // SCR1_TDU_ICOUNT_EN

// TDU CSRs
//------------------------------------------------------------------------------

// TSELECT register
logic                                           csr_tselect_upd;
logic [ALLTRIG_W-1:0]                           csr_tselect_ff;

// MCONTROL register
logic [MTRIG_NUM-1:0]                           csr_mcontrol_wr_req;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_clk_en;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_upd;

logic [MTRIG_NUM-1:0]                           csr_mcontrol_dmode_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_dmode_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_m_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_m_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_exec_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_exec_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_load_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_load_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_store_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_store_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_action_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_action_next;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_hit_ff;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_hit_next;

logic [MTRIG_NUM-1:0]                           csr_mcontrol_exec_hit;
logic [MTRIG_NUM-1:0]                           csr_mcontrol_ldst_hit;

// ICOUNT register
`ifdef SCR1_TDU_ICOUNT_EN
logic                                           csr_icount_wr_req;
logic                                           csr_icount_clk_en;
logic                                           csr_icount_upd;

logic                                           csr_icount_dmode_ff;
logic                                           csr_icount_dmode_next;
logic                                           csr_icount_m_ff;
logic                                           csr_icount_m_next;
logic                                           csr_icount_action_ff;
logic                                           csr_icount_action_next;
logic                                           csr_icount_hit_ff;
logic                                           csr_icount_hit_next;
logic [SCR1_TDU_ICOUNT_COUNT_HI-SCR1_TDU_ICOUNT_COUNT_LO:0]
                                                csr_icount_count_ff;
logic [SCR1_TDU_ICOUNT_COUNT_HI-SCR1_TDU_ICOUNT_COUNT_LO:0]
                                                csr_icount_count_next;
logic                                           csr_icount_skip_ff;
logic                                           csr_icount_skip_next;

logic                                           csr_icount_decr_en;
logic                                           csr_icount_count_decr;
logic                                           csr_icount_skip_dsbl;
logic                                           csr_icount_hit;
`endif // SCR1_TDU_ICOUNT_EN

// TDATA2 register
logic [MTRIG_NUM-1:0]                           csr_tdata2_upd;
logic [MTRIG_NUM-1:0] [SCR1_TDU_DATA_W-1:0]     csr_tdata2_ff;

//------------------------------------------------------------------------------
// CSR read/write interface
//------------------------------------------------------------------------------

// Read logic
//------------------------------------------------------------------------------

assign tdu2csr_resp_o = csr2tdu_req_i ? SCR1_CSR_RESP_OK : SCR1_CSR_RESP_ER;

always_comb begin
    tdu2csr_rdata_o = '0;
    if (csr2tdu_req_i) begin
        case (csr2tdu_addr_i)
            SCR1_CSR_ADDR_TDU_OFFS_TSELECT: begin
                tdu2csr_rdata_o = {'0, csr_tselect_ff};
            end
            SCR1_CSR_ADDR_TDU_OFFS_TDATA2 : begin
                for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
                    if(csr_tselect_ff == ALLTRIG_W'(i)) begin
                        tdu2csr_rdata_o = csr_tdata2_ff[i];
                    end
                end
            end
            SCR1_CSR_ADDR_TDU_OFFS_TDATA1 : begin
                for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
                    if(csr_tselect_ff == ALLTRIG_W'(i)) begin
                        tdu2csr_rdata_o[SCR1_TDU_TDATA1_TYPE_HI:
                                       SCR1_TDU_TDATA1_TYPE_LO]      = SCR1_TDU_MCONTROL_TYPE_VAL;
                        tdu2csr_rdata_o[SCR1_TDU_TDATA1_DMODE]       = csr_mcontrol_dmode_ff[i];
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_MASKMAX_HI:
                                       SCR1_TDU_MCONTROL_MASKMAX_LO] = SCR1_TDU_MCONTROL_MASKMAX_VAL;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_HIT]       = csr_mcontrol_hit_ff[i];
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_SELECT]    = SCR1_TDU_MCONTROL_SELECT_VAL;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_TIMING]    = SCR1_TDU_MCONTROL_TIMING_VAL;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_ACTION_HI:
                                       SCR1_TDU_MCONTROL_ACTION_LO]  = {5'b0, csr_mcontrol_action_ff[i]};
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_CHAIN]     = 1'b0;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_MATCH_HI:
                                       SCR1_TDU_MCONTROL_MATCH_LO]   = 4'b0;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_M]         = csr_mcontrol_m_ff[i];
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_RESERVEDA] = SCR1_TDU_MCONTROL_RESERVEDA_VAL;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_S]         = 1'b0;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_U]         = 1'b0;
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_EXECUTE]   = csr_mcontrol_exec_ff [i];
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_STORE]     = csr_mcontrol_store_ff[i];
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_LOAD]      = csr_mcontrol_load_ff [i];
                    end
                end
`ifdef SCR1_TDU_ICOUNT_EN
                if(csr_tselect_ff == ALLTRIG_W'(SCR1_TDU_ALLTRIG_NUM - 1'b1)) begin
                    tdu2csr_rdata_o[SCR1_TDU_TDATA1_TYPE_HI:
                                   SCR1_TDU_TDATA1_TYPE_LO]    = SCR1_TDU_ICOUNT_TYPE_VAL;
                    tdu2csr_rdata_o[SCR1_TDU_TDATA1_DMODE]     = csr_icount_dmode_ff;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_HIT]       = csr_icount_hit_ff;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_COUNT_HI:
                                   SCR1_TDU_ICOUNT_COUNT_LO]   = csr_icount_count_ff;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_U]         = 1'b0;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_S]         = 1'b0;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_M]         = csr_icount_m_ff;
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_ACTION_HI:
                                   SCR1_TDU_ICOUNT_ACTION_LO]  = {5'b0, csr_icount_action_ff};
                end
`endif // SCR1_TDU_ICOUNT_EN
            end
            SCR1_CSR_ADDR_TDU_OFFS_TINFO : begin
                for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
                    if(csr_tselect_ff == ALLTRIG_W'(i)) begin
                        tdu2csr_rdata_o[SCR1_TDU_MCONTROL_TYPE_VAL] = 1'b1;
                    end
                end
`ifdef SCR1_TDU_ICOUNT_EN
                if(csr_tselect_ff == ALLTRIG_W'(SCR1_TDU_ALLTRIG_NUM - 1'b1)) begin
                    tdu2csr_rdata_o[SCR1_TDU_ICOUNT_TYPE_VAL] = 1'b1;
                end
`endif // SCR1_TDU_ICOUNT_EN
            end
            default : begin
            end
        endcase
    end
end

// Write logic
//------------------------------------------------------------------------------

always_comb begin
    csr_wr_req  = 1'b0;
    csr_wr_data = '0;

    case (csr2tdu_cmd_i)
        SCR1_CSR_CMD_WRITE: begin
            csr_wr_req  = 1'b1;
            csr_wr_data = csr2tdu_wdata_i;
        end
        SCR1_CSR_CMD_SET  : begin
            csr_wr_req  = |csr2tdu_wdata_i;
            csr_wr_data = tdu2csr_rdata_o | csr2tdu_wdata_i;
        end
        SCR1_CSR_CMD_CLEAR: begin
            csr_wr_req  = |csr2tdu_wdata_i;
            csr_wr_data = tdu2csr_rdata_o & ~csr2tdu_wdata_i;
        end
        default : begin
        end
    endcase
end

// Register selection
//------------------------------------------------------------------------------

always_comb begin
    csr_addr_tselect  = 1'b0;
    csr_addr_tdata2   = '0;
    csr_addr_mcontrol = '0;
`ifdef SCR1_TDU_ICOUNT_EN
    csr_addr_icount   = '0;
`endif // SCR1_TDU_ICOUNT_EN

    if (csr2tdu_req_i) begin
        case (csr2tdu_addr_i)
            SCR1_CSR_ADDR_TDU_OFFS_TSELECT: begin
                csr_addr_tselect = 1'b1;
            end
            SCR1_CSR_ADDR_TDU_OFFS_TDATA1 : begin
                for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
                    if(csr_tselect_ff == ALLTRIG_W'(i)) begin
                        csr_addr_mcontrol[i] = 1'b1;
                    end
                end
`ifdef SCR1_TDU_ICOUNT_EN
                if(csr_tselect_ff == ALLTRIG_W'(SCR1_TDU_ALLTRIG_NUM - 1'b1)) begin
                    csr_addr_icount = 1'b1;
                end
`endif // SCR1_TDU_ICOUNT_EN
            end
            SCR1_CSR_ADDR_TDU_OFFS_TDATA2 : begin
                for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
                    if(csr_tselect_ff == ALLTRIG_W'(i) ) begin
                        csr_addr_tdata2[i] = 1'b1;
                    end
                end
            end
            default : begin
            end
        endcase
    end
end

//------------------------------------------------------------------------------
// TDU CSRs
//------------------------------------------------------------------------------
//
 // TDU CSRs consist of the following registers:
 // - TSELECT
 // - TDATA1/MCONTROL/ICOUNT (depending on the type field value)
 // - TDATA2
//

// TSELECT register
//------------------------------------------------------------------------------
// Determines which trigger is accessible through the other trigger registers

assign csr_tselect_upd = clk_en & csr_addr_tselect & csr_wr_req
                       & (csr_wr_data[ALLTRIG_W-1:0] < ALLTRIG_W'(ALLTRIG_NUM));

always_ff @(negedge rst_n, posedge clk) begin
    if(~rst_n) begin
        csr_tselect_ff <= '0;
    end else if(csr_tselect_upd) begin
        csr_tselect_ff <= csr_wr_data[ALLTRIG_W-1:0];
    end
end

`ifdef SCR1_TDU_ICOUNT_EN
// ICOUNT register
//------------------------------------------------------------------------------
// Provides a trigger that fires when the certain number of instructions has retired
// Is intended to be used as a single step trigger (in this case count must be 1)

assign csr_icount_wr_req = csr_addr_icount & csr_wr_req;
assign csr_icount_clk_en = clk_en & (csr_icount_wr_req | csr_icount_m_ff);
assign csr_icount_upd    = ~csr_icount_dmode_ff
                         ? csr_icount_wr_req
                         : tdu_dsbl_i & csr_icount_wr_req;

always_ff @(negedge rst_n, posedge clk) begin
    if(~rst_n) begin
        csr_icount_dmode_ff  <= 1'b0;
        csr_icount_m_ff      <= 1'b0;
        csr_icount_action_ff <= 1'b0;
        csr_icount_hit_ff    <= 1'b0;
        csr_icount_count_ff  <= '0;
        csr_icount_skip_ff   <= 1'b0;
    end else if (csr_icount_clk_en) begin
        csr_icount_dmode_ff  <= csr_icount_dmode_next;
        csr_icount_m_ff      <= csr_icount_m_next;
        csr_icount_action_ff <= csr_icount_action_next;
        csr_icount_hit_ff    <= csr_icount_hit_next;
        csr_icount_count_ff  <= csr_icount_count_next;
        csr_icount_skip_ff   <= csr_icount_skip_next;
    end
end

assign csr_icount_decr_en    = (~tdu_dsbl_i & csr_icount_m_ff)
                             ? exu2tdu_imon_i.vd & (csr_icount_count_ff != 14'b0)
                             : 1'b0;
assign csr_icount_count_decr = exu2tdu_imon_i.req & csr_icount_decr_en & ~csr_icount_skip_ff;
assign csr_icount_skip_dsbl  = exu2tdu_imon_i.req & csr_icount_decr_en & csr_icount_skip_ff;

always_comb begin
    if (csr_icount_upd) begin
        csr_icount_dmode_next  = csr_wr_data[SCR1_TDU_TDATA1_DMODE];
        csr_icount_m_next      = csr_wr_data[SCR1_TDU_ICOUNT_M];
        csr_icount_action_next = (csr_wr_data[SCR1_TDU_ICOUNT_ACTION_HI
                                             :SCR1_TDU_ICOUNT_ACTION_LO] == 'b1);
        csr_icount_hit_next    = csr_wr_data[SCR1_TDU_ICOUNT_HIT];
        csr_icount_count_next  = csr_wr_data[SCR1_TDU_ICOUNT_COUNT_HI:SCR1_TDU_ICOUNT_COUNT_LO];
    end else begin
        csr_icount_dmode_next  = csr_icount_dmode_ff;
        csr_icount_m_next      = csr_icount_m_ff;
        csr_icount_action_next = csr_icount_action_ff;
        csr_icount_hit_next    = exu2tdu_bp_retire_i[ALLTRIG_NUM - 1'b1]
                               ? 1'b1
                               : csr_icount_hit_ff;
        csr_icount_count_next  = csr_icount_count_decr
                               ? csr_icount_count_ff - 1'b1
                               : csr_icount_count_ff;
    end
end

assign csr_icount_skip_next = csr_icount_wr_req    ? csr_wr_data[SCR1_TDU_ICOUNT_M]
                            : csr_icount_skip_dsbl ? 1'b0
                                                   : csr_icount_skip_ff;
`endif // SCR1_TDU_ICOUNT_EN

// MCONTROL registers
//------------------------------------------------------------------------------
// Provides a trigger that fires on the virtual address (stored in TDATA2) match
// (load, store, exec options supported). Triggers chaining supported

genvar trig;
generate
for (trig = 0; $unsigned(trig) < MTRIG_NUM; ++trig) begin : gblock_mtrig

assign csr_mcontrol_wr_req[trig] = csr_addr_mcontrol[trig] & csr_wr_req;
assign csr_mcontrol_clk_en[trig] = clk_en
                                 & (csr_mcontrol_wr_req[trig] | csr_mcontrol_m_ff[trig]);
assign csr_mcontrol_upd   [trig] = ~csr_mcontrol_dmode_ff[trig]
                                 ? csr_mcontrol_wr_req[trig]
                                 : tdu_dsbl_i & csr_mcontrol_wr_req[trig];

always_ff @(negedge rst_n, posedge clk) begin
    if(~rst_n) begin
        csr_mcontrol_dmode_ff [trig] <= 1'b0;
        csr_mcontrol_m_ff     [trig] <= 1'b0;
        csr_mcontrol_exec_ff  [trig] <= 1'b0;
        csr_mcontrol_load_ff  [trig] <= 1'b0;
        csr_mcontrol_store_ff [trig] <= 1'b0;
        csr_mcontrol_action_ff[trig] <= 1'b0;
        csr_mcontrol_hit_ff   [trig] <= 1'b0;
    end else if(csr_mcontrol_clk_en[trig]) begin
        csr_mcontrol_dmode_ff [trig] <= csr_mcontrol_dmode_next[trig];
        csr_mcontrol_m_ff     [trig] <= csr_mcontrol_m_next[trig];
        csr_mcontrol_exec_ff  [trig] <= csr_mcontrol_exec_next[trig];
        csr_mcontrol_load_ff  [trig] <= csr_mcontrol_load_next[trig];
        csr_mcontrol_store_ff [trig] <= csr_mcontrol_store_next[trig];
        csr_mcontrol_action_ff[trig] <= csr_mcontrol_action_next[trig];
        csr_mcontrol_hit_ff   [trig] <= csr_mcontrol_hit_next[trig];
    end
end

always_comb begin
    if (csr_mcontrol_upd[trig]) begin
        csr_mcontrol_dmode_next [trig] = csr_wr_data[SCR1_TDU_TDATA1_DMODE];
        csr_mcontrol_m_next     [trig] = csr_wr_data[SCR1_TDU_MCONTROL_M];
        csr_mcontrol_exec_next  [trig] = csr_wr_data[SCR1_TDU_MCONTROL_EXECUTE];
        csr_mcontrol_load_next  [trig] = csr_wr_data[SCR1_TDU_MCONTROL_LOAD];
        csr_mcontrol_store_next [trig] = csr_wr_data[SCR1_TDU_MCONTROL_STORE];
        csr_mcontrol_action_next[trig] = (csr_wr_data[SCR1_TDU_MCONTROL_ACTION_HI
                                                     :SCR1_TDU_MCONTROL_ACTION_LO] == 'b1);
        csr_mcontrol_hit_next   [trig] = csr_wr_data[SCR1_TDU_MCONTROL_HIT];
    end else begin
        csr_mcontrol_dmode_next [trig] = csr_mcontrol_dmode_ff [trig];
        csr_mcontrol_m_next     [trig] = csr_mcontrol_m_ff     [trig];
        csr_mcontrol_exec_next  [trig] = csr_mcontrol_exec_ff  [trig];
        csr_mcontrol_load_next  [trig] = csr_mcontrol_load_ff  [trig];
        csr_mcontrol_store_next [trig] = csr_mcontrol_store_ff [trig];
        csr_mcontrol_action_next[trig] = csr_mcontrol_action_ff[trig];
        csr_mcontrol_hit_next   [trig] = exu2tdu_bp_retire_i[trig]
                                       ? 1'b1
                                       : csr_mcontrol_hit_ff[trig];
    end
end

// TDATA2 register
//------------------------------------------------------------------------------

assign csr_tdata2_upd[trig] = ~csr_mcontrol_dmode_ff[trig]
                            ? clk_en & csr_addr_tdata2[trig] & csr_wr_req
                            : clk_en & csr_addr_tdata2[trig] & csr_wr_req & tdu_dsbl_i;

always_ff @(posedge clk) begin
    if (csr_tdata2_upd[trig]) begin
        csr_tdata2_ff[trig] <= csr_wr_data;
    end
end

end
endgenerate // gblock_mtrig

//------------------------------------------------------------------------------
// TDU <-> EXU interface
//------------------------------------------------------------------------------

assign csr_icount_hit = ~tdu_dsbl_i & csr_icount_m_ff
                      ? exu2tdu_imon_i.vd & (csr_icount_count_ff == 14'b1) & ~csr_icount_skip_ff
                      : 1'b0;

`ifndef SCR1_TDU_ICOUNT_EN
assign tdu2exu_ibrkpt_match_o   = csr_mcontrol_exec_hit;
assign tdu2exu_ibrkpt_exc_req_o = |csr_mcontrol_exec_hit;
`else
assign tdu2exu_ibrkpt_match_o   = {csr_icount_hit, csr_mcontrol_exec_hit};
assign tdu2exu_ibrkpt_exc_req_o = |csr_mcontrol_exec_hit | csr_icount_hit;
`endif // SCR1_TDU_ICOUNT_EN

//------------------------------------------------------------------------------
// TDU <-> LSU interface
//------------------------------------------------------------------------------

// Breakpoint logic
//------------------------------------------------------------------------------

generate
for (trig = 0; $unsigned(trig) < MTRIG_NUM; ++trig) begin : gblock_break_trig
assign csr_mcontrol_exec_hit[trig] = ~tdu_dsbl_i
                                   & csr_mcontrol_m_ff[trig]
                                   & csr_mcontrol_exec_ff[trig]
                                   & exu2tdu_imon_i.vd
                                   & exu2tdu_imon_i.addr == csr_tdata2_ff[trig];
end
endgenerate

`ifndef SCR1_TDU_ICOUNT_EN
assign tdu2lsu_ibrkpt_exc_req_o = |csr_mcontrol_exec_hit;
`else
assign tdu2lsu_ibrkpt_exc_req_o = |csr_mcontrol_exec_hit | csr_icount_hit;
`endif // SCR1_TDU_ICOUNT_EN

// Watchpoint logic
//------------------------------------------------------------------------------

generate
for( trig = 0; $unsigned(trig) < MTRIG_NUM; ++trig ) begin : gblock_watch_trig
assign csr_mcontrol_ldst_hit[trig] = ~tdu_dsbl_i
                                   & csr_mcontrol_m_ff[trig]
                                   & lsu2tdu_dmon_i.vd
                                   & ( (csr_mcontrol_load_ff [trig] & lsu2tdu_dmon_i.load)
                                     | (csr_mcontrol_store_ff[trig] & lsu2tdu_dmon_i.store))
                                   & lsu2tdu_dmon_i.addr == csr_tdata2_ff[trig];
end
endgenerate

assign tdu2lsu_dbrkpt_match_o   = csr_mcontrol_ldst_hit;
assign tdu2lsu_dbrkpt_exc_req_o = |csr_mcontrol_ldst_hit;

`ifndef SCR1_TDU_EN
assign tdu2lsu_brk_en_o = |csr_mcontrol_m_ff | csr_icount_m_ff;
`endif // SCR1_TDU_EN

//------------------------------------------------------------------------------
// TDU <-> HDU interface
//------------------------------------------------------------------------------

always_comb begin
    tdu2hdu_dmode_req_o = 1'b0;

    for(int unsigned i = 0; i < MTRIG_NUM; ++i) begin
        tdu2hdu_dmode_req_o |= (csr_mcontrol_action_ff[i] & exu2tdu_bp_retire_i[i]);
    end
`ifdef SCR1_TDU_ICOUNT_EN
    tdu2hdu_dmode_req_o |= (csr_icount_action_ff & exu2tdu_bp_retire_i[ALLTRIG_NUM-1]);
`endif // SCR1_TDU_ICOUNT_EN
end

`ifdef SCR1_TRGT_SIMULATION
//------------------------------------------------------------------------------
// Assertion
//------------------------------------------------------------------------------

SVA_TDU_X_CONTROL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({clk_en, tdu_dsbl_i, csr2tdu_req_i,
                 exu2tdu_imon_i.vd, lsu2tdu_dmon_i.vd, exu2tdu_bp_retire_i})
    ) else $error("TDU Error: control signals is X - %0b", {clk_en,
    tdu_dsbl_i, csr2tdu_req_i, exu2tdu_imon_i.vd, lsu2tdu_dmon_i.vd, exu2tdu_bp_retire_i});

SVA_DM_X_CLK_EN : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(clk_en)
    ) else $error("TDU Error: clk_en control signals is X");

SVA_DM_X_DSBL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(tdu_dsbl_i)
    ) else $error("TDU Error: tdu_dsbl_i control signals is X");

SVA_DM_X_CSR2TDU_REQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(csr2tdu_req_i)
    ) else $error("TDU Error: csr2tdu_req_i control signals is X");

SVA_DM_X_I_MON_VD : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(exu2tdu_imon_i.vd)
    ) else $error("TDU Error: exu2tdu_imon_i.vd control signals is X");

SVA_DM_X_D_MON_VD : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(lsu2tdu_dmon_i.vd)
    ) else $error("TDU Error: lsu2tdu_dmon_i.vd control signals is X");

SVA_DM_X_BP_RETIRE : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown(exu2tdu_bp_retire_i)
    ) else $error("TDU Error: exu2tdu_bp_retire_i control signals is X");

SVA_TDU_X_CSR : assert property (
    @(negedge clk) disable iff (~rst_n)
    csr2tdu_req_i |-> !$isunknown({csr2tdu_cmd_i,csr2tdu_addr_i})
    ) else $error("TDU Error: csr is X");

SVA_TDU_XW_CSR : assert property (
    @(negedge clk) disable iff (~rst_n)
    (csr2tdu_req_i & csr_wr_req) |-> !$isunknown(csr2tdu_wdata_i)
    ) else $error("TDU Error: csr wdata is X ");

SVA_TDU_X_IMON : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2tdu_imon_i.vd |-> !$isunknown({exu2tdu_imon_i.req,exu2tdu_imon_i.addr})
    ) else $error("TDU Error: imonitor is X");

SVA_TDU_X_DMON : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2tdu_dmon_i.vd |-> !$isunknown({lsu2tdu_dmon_i})
    ) else $error("TDU Error: dmonitor is X");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_tdu

`endif // SCR1_TDU_EN

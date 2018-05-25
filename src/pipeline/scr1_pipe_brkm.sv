/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_brkm.sv>
/// @brief      Hardware Breakpoint Module (BRKM)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_BRKM_EN
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_brkm.svh"

module scr1_pipe_brkm (
    // Common
    input   logic                                       rst_n,                  // Module's global reset
    input   logic                                       clk,                    // Module's clock
    input   logic                                       clk_en,                 // Clock Enable line
    input   logic                                       init,                   // Initialization of Instruction BP Skipping mechanism
    input   logic                                       dsbl,                   // BRKM disable
    //  CSR <-> BRKM interface
    input   logic                                       csr2brkm_req,           // BRKM CSR access request active
    input   type_scr1_csr_cmd_sel_e                     csr2brkm_cmd,           // CSR access command
    input   logic [SCR1_BRKM_PKG_CSR_OFFS_WIDTH-1:0]    csr2brkm_addr,          // Offset within CSRs block
    input   logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr2brkm_wdata,         // Write Data
    output  logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    brkm2csr_rdata,         // Read Data
    output  type_scr1_csr_resp_e                        brkm2csr_resp,          // Read Response code
    // EXU/LSU <-> BRKM interface
    input   type_scr1_brkm_instr_mon_s                  exu2brkm_i_mon,         // Instruction Stream Monitoring structure
    output  logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      brkm2exu_i_match,       // Instruction Breakpoint Match flag
    output  logic                                       brkm2exu_i_x_req,       // Instruction Breakpoint Request (for EXU)
    output  logic                                       lsu_brk_en,             // Breakpoint Enabled Flag (1 if at least 1 BP is active)
    output  logic                                       brkm2lsu_i_x_req,       // Instruction Breakpoint Request (for LSU)
    input   type_scr1_brkm_lsu_mon_s                    lsu2brkm_d_mon,         // Load/Store Stream Monitoring structure
    output  logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      brkm2lsu_d_match,       // Load/Store Breakpoint Match flag
    output  logic                                       brkm2lsu_d_x_req,       // Load/Store Breakpoint Request
    input   logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      exu2brkm_bp_retire,     // Instruction with Breakpoint Retirement flag
    input   logic                                       exu2brkm_bp_i_recover,  // Instruction Breakpoint Recovering flag
    // DBGA <-> BRKM interface
    output  logic                                       brkm2dbga_dmode_req     // Debug Mode Transition Request
);

//-------------------------------------------------------------------------------
// Configuration parameters declaration
//-------------------------------------------------------------------------------
localparam bit                       BRKM_CFG_SUPP_OPER_EXEC            = SCR1_BRKM_PKG_SUPP_OPER_EXEC;
localparam bit                       BRKM_CFG_SUPP_OPER_LOAD            = SCR1_BRKM_PKG_SUPP_OPER_LOAD;
localparam bit                       BRKM_CFG_SUPP_OPER_STORE           = SCR1_BRKM_PKG_SUPP_OPER_STORE;
localparam bit                       BRKM_CFG_SUPP_ADDR_EXACT           = SCR1_BRKM_PKG_SUPP_ADDR_EXACT;
localparam bit                       BRKM_CFG_SUPP_ADDR_MASK            = SCR1_BRKM_PKG_SUPP_ADDR_MASK;
localparam bit                       BRKM_CFG_SUPP_ADDR_MASK_EXT_EXEC   = SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_EXEC;
localparam bit                       BRKM_CFG_SUPP_ADDR_MASK_EXT_LDST   = SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_LDST;
localparam type_scr1_op_width_e      BRKM_CFG_EXEC_OPWIDTH_MAX          = SCR1_OP_WIDTH_WORD;
localparam int unsigned              BRKM_CFG_EXEC_ADDR_WIDTH           = SCR1_BRKM_PKG_EXEC_ADDR_WIDTH;
localparam type_scr1_op_width_e      BRKM_CFG_LDST_OPWIDTH_MAX          = SCR1_OP_WIDTH_WORD;
localparam int unsigned              BRKM_CFG_LDST_ADDR_WIDTH           = SCR1_BRKM_PKG_LDST_ADDR_WIDTH;

genvar bp;

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------
localparam int BRKM_LCL_BRKPT_ID_WIDTH      = $signed((SCR1_BRKM_PKG_BRKPT_NUMBER > 'd1)
                                            ? $clog2(SCR1_BRKM_PKG_BRKPT_NUMBER)
                                            : (SCR1_BRKM_PKG_BRKPT_NUMBER));

localparam bit BRKM_LCL_WATCH_EXEC          = BRKM_CFG_SUPP_OPER_EXEC;

localparam bit BRKM_LCL_WATCH_LDST          = BRKM_CFG_SUPP_OPER_LOAD
                                            | BRKM_CFG_SUPP_OPER_STORE;

localparam bit BRKM_LCL_WATCH_ADDR          = BRKM_CFG_SUPP_ADDR_EXACT
                                            | BRKM_CFG_SUPP_ADDR_MASK;

localparam bit BRKM_LCL_MATCH_ADDR_MASK_EXT = BRKM_CFG_SUPP_ADDR_MASK_EXT_EXEC
                                            | BRKM_CFG_SUPP_ADDR_MASK_EXT_LDST;

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
// CSRs :: bpselect
typedef struct packed {
    logic [BRKM_LCL_BRKPT_ID_WIDTH-1 : 0]   bp;
} l_type_brkm_csr_bpselect_reg_s;

// CSRs :: bpcontrol
typedef struct packed {
    logic                                   matched;
    type_scr1_brkm_csr_bpcontrol_action_e   action;
} l_type_brkm_csr_bpcontrol_invrnt_reg_s;

// CSRs :: bpctrlext
typedef struct packed {
    logic                                   dry_run;
} l_type_brkm_csr_bpctrlext_reg_s;

// CSRs :: brkmctrl
typedef struct packed {
    logic                                   mode;
    logic                                   init;
    logic                                   bp_i_skip;
} l_type_brkm_csr_brkmctrl_reg_s;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
// -- CSRs ----------------------------------------------------------------------
// CSRs :: common
logic                                       csr_wr;
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_wr_data;
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_rd_data;
// CSRs :: bpselect
logic                                       csr_bpselect_sel;
logic                                       csr_bpselect_wr;
l_type_brkm_csr_bpselect_reg_s              csr_bpselect_reg;
type_scr1_brkm_csr_bpselect_s               csr_bpselect_in;
type_scr1_brkm_csr_bpselect_s               csr_bpselect_out;

// CSRs :: bpcontrol
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_sel;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_wr;
l_type_brkm_csr_bpcontrol_invrnt_reg_s      csr_bpcontrol_invrnt_reg[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
type_scr1_brkm_csr_bpcontrol_s              csr_bpcontrol_in [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
type_scr1_brkm_csr_bpcontrol_s              csr_bpcontrol_out[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];

// CSRs :: bpcontrol
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_execen_reg;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_loaden_reg;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_storeen_reg;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_aen_reg;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpcontrol_amasken_reg;

// CSRs :: bploaddr
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bploaddr_sel;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bploaddr_wr;
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bploaddr_reg[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bploaddr_in [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bploaddr_out[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];

// CSRs :: bphiaddr
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bphiaddr_sel;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bphiaddr_wr;
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bphiaddr_reg[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bphiaddr_in [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr_bphiaddr_out[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];

// CSRs :: bpctrlext
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpctrlext_sel;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpctrlext_wr;
l_type_brkm_csr_bpctrlext_reg_s             csr_bpctrlext_reg[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
type_scr1_brkm_csr_bpctrlext_s              csr_bpctrlext_in [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
type_scr1_brkm_csr_bpctrlext_s              csr_bpctrlext_out[SCR1_BRKM_PKG_BRKPT_NUMBER-1:0];
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpctrlext_arangeen_reg;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      csr_bpctrlext_amasken_reg;

// CSRs :: brkmctrl
logic                                       csr_brkmctrl_sel;
logic                                       csr_brkmctrl_wr;
l_type_brkm_csr_brkmctrl_reg_s              csr_brkmctrl_reg;
type_scr1_brkm_csr_brkmctrl_s               csr_brkmctrl_in;
type_scr1_brkm_csr_brkmctrl_s               csr_brkmctrl_out;

// -- BP Array ------------------------------------------------------------------
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      ma_i_valid;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      ma_i_match;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      ma_d_valid;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      ma_d_match;

// -- iBP Skip ------------------------------------------------------------------
logic                                       ibpskip_state_reg;

// -- BP Management -------------------------------------------------------------
logic                                       bpmngt_init;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      bpmngt_bp_en;
logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0]      bpmngt_bp_matched_set;
logic                                       bpmngt_bp_i_match;


//-------------------------------------------------------------------------------
// CSRs :: Interface
//-------------------------------------------------------------------------------

// CSRs :: Interface :: Reg Select
always_comb begin
    csr_bpselect_sel    = 1'b0;
    csr_brkmctrl_sel    = 1'b0;
    csr_bpcontrol_sel   = '0;
    csr_bploaddr_sel    = '0;
    csr_bphiaddr_sel    = '0;
    csr_bpctrlext_sel   = '0;

    if (csr2brkm_req) begin
        case (csr2brkm_addr)
            SCR1_BRKM_PKG_CSR_OFFS_BPSELECT : begin
                csr_bpselect_sel    = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_OFFS_BPCONTROL : begin
                csr_bpcontrol_sel[csr_bpselect_reg.bp]  = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_OFFS_BPLOADDR : begin
                csr_bploaddr_sel[csr_bpselect_reg.bp]   = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_OFFS_BPHIADDR : begin
                csr_bphiaddr_sel[csr_bpselect_reg.bp]   = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_OFFS_BPLODATA,
            SCR1_BRKM_PKG_CSR_OFFS_BPHIDATA : begin
                // Writing is ignored
            end

            SCR1_BRKM_PKG_CSR_OFFS_BPCTRLEXT : begin
                csr_bpctrlext_sel[csr_bpselect_reg.bp]  = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_OFFS_BRKMCTRL : begin
                csr_brkmctrl_sel                        = 1'b1;
            end

            default : begin
                csr_bpselect_sel    = 1'b0;
                csr_brkmctrl_sel    = 1'b0;
                csr_bpcontrol_sel   = '0;
                csr_bploaddr_sel    = '0;
                csr_bphiaddr_sel    = '0;
                csr_bpctrlext_sel   = '0;
            end
        endcase
    end
end

// CSRs :: Interface :: Read Data
always_comb begin
    logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]   csr_bpcontrol_out_l;
    logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]   csr_bploaddr_out_l;
    logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]   csr_bphiaddr_out_l;
    logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]   csr_bpctrlext_out_l;

    csr_bpcontrol_out_l = '0;
    csr_bploaddr_out_l  = '0;
    csr_bphiaddr_out_l  = '0;
    csr_bpctrlext_out_l = '0;

    for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
        csr_bpcontrol_out_l |= csr_bpcontrol_out[i];
        csr_bploaddr_out_l  |= csr_bploaddr_out[i];
        csr_bphiaddr_out_l  |= csr_bphiaddr_out[i];
        csr_bpctrlext_out_l |= csr_bpctrlext_out[i];
    end

    csr_rd_data     = csr_bpselect_out
                    | csr_brkmctrl_out
                    | csr_bpcontrol_out_l
                    | csr_bploaddr_out_l
                    | csr_bphiaddr_out_l
                    | csr_bpctrlext_out_l;
end

// CSRs :: Interface :: Writing
always_comb begin
    csr_wr          = 1'b0;
    csr_wr_data     = 1'b0;

    if (csr2brkm_req) begin
        case (csr2brkm_cmd)
            SCR1_CSR_CMD_WRITE : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr2brkm_wdata;
            end

            SCR1_CSR_CMD_SET : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr_rd_data | ( csr2brkm_wdata);
            end

            SCR1_CSR_CMD_CLEAR : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr_rd_data & (~csr2brkm_wdata);
            end

            default : begin
                csr_wr_data     = '0;
            end
        endcase
    end
end

// CSRs :: Interface :: Response
assign brkm2csr_resp    = (csr2brkm_req) ? SCR1_CSR_RESP_OK : SCR1_CSR_RESP_ER;
assign brkm2csr_rdata   = csr_rd_data;

//-------------------------------------------------------------------------------
// CSRs :: bpselect
//-------------------------------------------------------------------------------
generate

if (BRKM_LCL_BRKPT_ID_WIDTH > 1)
begin : gen_csr_bpselect

always_comb begin
    csr_bpselect_wr     = csr_bpselect_sel & csr_wr;
    csr_bpselect_in     = csr_wr_data;
    //
    csr_bpselect_out    = '0;
    if (csr_bpselect_sel) begin
        csr_bpselect_out.bp[0+:BRKM_LCL_BRKPT_ID_WIDTH] = csr_bpselect_reg.bp;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_bpselect_reg            <= '0;
    end
    else begin
        if (clk_en) begin
            if (csr_bpselect_wr) begin
                csr_bpselect_reg.bp <= csr_bpselect_in[0+:BRKM_LCL_BRKPT_ID_WIDTH];
            end
        end
    end
end

end : gen_csr_bpselect
else // (BRKM_LCL_BRKPT_ID_WIDTH == 1)
begin : gen_csr_bpselect

always_comb begin
    csr_bpselect_wr     = csr_bpselect_sel & csr_wr;
    csr_bpselect_in     = csr_wr_data;
    //
    csr_bpselect_out    = '0;
    if (csr_bpselect_sel) begin
        csr_bpselect_out.bp[0] = csr_bpselect_reg.bp;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_bpselect_reg            <= '0;
    end
    else begin
        if (clk_en) begin
            if (csr_bpselect_wr) begin
                csr_bpselect_reg.bp <= csr_bpselect_in[0];
            end
        end
    end
end

end : gen_csr_bpselect

endgenerate

//-------------------------------------------------------------------------------
// CSRs :: bpcontrol[]
//-------------------------------------------------------------------------------
always_comb begin
    csr_bpcontrol_wr         = '0;
    for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
        csr_bpcontrol_wr[i]  = csr_bpcontrol_sel[i] & csr_wr;
        csr_bpcontrol_in[i]  = csr_wr_data;
        csr_bpcontrol_out[i] = '0;
        //
        if (csr_bpcontrol_sel[i]) begin
            csr_bpcontrol_out[i].loadsup   = BRKM_CFG_SUPP_OPER_LOAD;
            csr_bpcontrol_out[i].storesup  = BRKM_CFG_SUPP_OPER_STORE;
            csr_bpcontrol_out[i].execsup   = BRKM_CFG_SUPP_OPER_EXEC;
            csr_bpcontrol_out[i].asup      = BRKM_CFG_SUPP_ADDR_EXACT;
            csr_bpcontrol_out[i].amasksup  = BRKM_CFG_SUPP_ADDR_MASK;
            //
            csr_bpcontrol_out[i].matched   = csr_bpcontrol_invrnt_reg[i].matched;
            csr_bpcontrol_out[i].action    = csr_bpcontrol_invrnt_reg[i].action;
            csr_bpcontrol_out[i].loaden    = csr_bpcontrol_loaden_reg[i];
            csr_bpcontrol_out[i].storeen   = csr_bpcontrol_storeen_reg[i];
            csr_bpcontrol_out[i].execen    = csr_bpcontrol_execen_reg[i];
            //
            csr_bpcontrol_out[i].aen       = csr_bpcontrol_aen_reg[i];
            csr_bpcontrol_out[i].amasken   = csr_bpcontrol_amasken_reg[i];
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bpcontrol_invrnt_reg[i].matched <= 1'b0;
            csr_bpcontrol_invrnt_reg[i].action  <= SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_NONE;
        end
    end
    else begin
        if (clk_en) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                if (csr_bpcontrol_wr[i]) begin
                    csr_bpcontrol_invrnt_reg[i].action  <= csr_bpcontrol_in[i].action;
                end
                if (  (csr_bpcontrol_wr[i])
                    & (   (   (~csr_brkmctrl_reg.mode)
                            & (~csr_bpcontrol_in[i].matched))
                        | (   ( csr_brkmctrl_reg.mode)
                            & ( csr_bpcontrol_in[i].matched))  )
                ) begin
                    csr_bpcontrol_invrnt_reg[i].matched <= 1'b0;
                end
                else if (bpmngt_bp_matched_set[i]) begin
                    csr_bpcontrol_invrnt_reg[i].matched <= 1'b1;
                end
            end
        end
    end
end

generate
if (BRKM_CFG_SUPP_OPER_EXEC)
begin : gen_bpcontrol_match_oper_exec
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpcontrol_execen_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpcontrol_wr[i]) begin
                        csr_bpcontrol_execen_reg[i]  <= csr_bpcontrol_in[i].execen;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_oper_exec
else
begin : gen_bpcontrol_match_oper_exec
    assign csr_bpcontrol_execen_reg = '0;
end : gen_bpcontrol_match_oper_exec

if (BRKM_CFG_SUPP_OPER_LOAD)
begin : gen_bpcontrol_match_oper_load
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpcontrol_loaden_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpcontrol_wr[i]) begin
                        csr_bpcontrol_loaden_reg[i]  <= csr_bpcontrol_in[i].loaden;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_oper_load
else
begin : gen_bpcontrol_match_oper_load
    assign csr_bpcontrol_loaden_reg = '0;
end : gen_bpcontrol_match_oper_load

if (BRKM_CFG_SUPP_OPER_STORE)
begin : gen_bpcontrol_match_oper_store
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpcontrol_storeen_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpcontrol_wr[i]) begin
                        csr_bpcontrol_storeen_reg[i]  <= csr_bpcontrol_in[i].storeen;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_oper_store
else
begin : gen_bpcontrol_match_oper_store
    assign csr_bpcontrol_storeen_reg = '0;
end : gen_bpcontrol_match_oper_store

if (BRKM_CFG_SUPP_ADDR_EXACT)
begin : gen_bpcontrol_match_addr_exact
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpcontrol_aen_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpcontrol_wr[i]) begin
                        csr_bpcontrol_aen_reg[i]  <= csr_bpcontrol_in[i].aen;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_addr_exact
else
begin : gen_bpcontrol_match_addr_exact
    assign csr_bpcontrol_aen_reg = '0;
end : gen_bpcontrol_match_addr_exact

if (BRKM_CFG_SUPP_ADDR_MASK)
begin : gen_bpcontrol_match_addr_mask
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int  unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpcontrol_amasken_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpcontrol_wr[i]) begin
                        csr_bpcontrol_amasken_reg[i]  <= csr_bpcontrol_in[i].amasken;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_addr_mask
else
begin : gen_bpcontrol_match_addr_mask
    assign csr_bpcontrol_amasken_reg = '0;
end : gen_bpcontrol_match_addr_mask

endgenerate

//-------------------------------------------------------------------------------
// CSRs :: bploaddr[]
//-------------------------------------------------------------------------------
generate
if (BRKM_CFG_SUPP_ADDR_EXACT)
begin : gen_bploaddr_match_addr_exact

    always_comb begin
        csr_bploaddr_wr     = '0;
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bploaddr_wr[i]  = csr_bploaddr_sel[i] & csr_wr;
            csr_bploaddr_in[i]  = csr_wr_data;
            csr_bploaddr_out[i] = '0;
            //
            if (csr_bploaddr_sel[i]) begin
                csr_bploaddr_out[i] = csr_bploaddr_reg[i];
            end
        end
    end

    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bploaddr_reg[i] <= '0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bploaddr_wr[i]) begin
                        csr_bploaddr_reg[i]  <= csr_bploaddr_in[i];
                    end
                end
            end
        end
    end
end : gen_bploaddr_match_addr_exact
else
begin : gen_bploaddr_match_addr_exact
    always_comb begin
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bploaddr_wr [i] = 1'b0;
            csr_bploaddr_in [i] = '0;
            csr_bploaddr_out[i] = '0;
            csr_bploaddr_reg[i] = '0;
        end
    end
end : gen_bploaddr_match_addr_exact
endgenerate

//-------------------------------------------------------------------------------
// CSRs :: bphiaddr[]
//-------------------------------------------------------------------------------
generate
if (BRKM_CFG_SUPP_ADDR_MASK)
begin : gen_bphiaddr_match_addr_range_or_mask

    always_comb begin
        csr_bphiaddr_wr     = '0;
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bphiaddr_wr[i]  = csr_bphiaddr_sel[i] & csr_wr;
            csr_bphiaddr_in[i]  = csr_wr_data;
            csr_bphiaddr_out[i] = '0;
            //
            if (csr_bphiaddr_sel[i]) begin
                csr_bphiaddr_out[i] = csr_bphiaddr_reg[i];
            end
        end
    end

    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bphiaddr_reg[i] <= '0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bphiaddr_wr[i]) begin
                        csr_bphiaddr_reg[i]  <= csr_bphiaddr_in[i];
                    end
                end
            end
        end
    end
end : gen_bphiaddr_match_addr_range_or_mask
else
begin : gen_bphiaddr_match_addr_range_or_mask
    always_comb begin
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bphiaddr_wr [i] = 1'b0;
            csr_bphiaddr_in [i] = '0;
            csr_bphiaddr_out[i] = '0;
            csr_bphiaddr_reg[i] = '0;
        end
    end
end : gen_bphiaddr_match_addr_range_or_mask
endgenerate

//-------------------------------------------------------------------------------
// CSRs :: bpctrlext[]
//-------------------------------------------------------------------------------
always_comb begin
    csr_bpctrlext_wr     = '0;
    for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
        csr_bpctrlext_wr[i]  = csr_bpctrlext_sel[i] & csr_wr;
        csr_bpctrlext_in[i]  = csr_wr_data;
        csr_bpctrlext_out[i] = '0;
        //
        if (csr_bpctrlext_sel[i]) begin
            csr_bpctrlext_out[i].arangeen   = csr_bpctrlext_arangeen_reg[i];
            csr_bpctrlext_out[i].amasken    = csr_bpctrlext_amasken_reg[i];
            csr_bpctrlext_out[i].dry_run    = csr_bpctrlext_reg[i].dry_run;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            csr_bpctrlext_reg[i] <= '0;
        end
    end
    else begin
        if (clk_en) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                if (csr_bpctrlext_wr[i]) begin
                    csr_bpctrlext_reg[i].dry_run <= csr_bpctrlext_in[i].dry_run;
                end
            end
        end
    end
end

generate

if (BRKM_LCL_MATCH_ADDR_MASK_EXT)
begin : gen_bpcontrol_match_addr_mask_ext
    always_ff @(negedge rst_n, posedge clk) begin
        if (~rst_n) begin
            for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                csr_bpctrlext_amasken_reg[i] <= 1'b0;
            end
        end
        else begin
            if (clk_en) begin
                for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
                    if (csr_bpctrlext_wr[i]) begin
                        csr_bpctrlext_amasken_reg[i]  <= csr_bpctrlext_in[i].amasken;
                    end
                end
            end
        end
    end
end : gen_bpcontrol_match_addr_mask_ext
else
begin : gen_bpcontrol_match_addr_mask_ext
    assign csr_bpctrlext_amasken_reg = '0;
end : gen_bpcontrol_match_addr_mask_ext

endgenerate

assign csr_bpctrlext_arangeen_reg = '0;

//-------------------------------------------------------------------------------
// CSRs :: brkmctrl
//-------------------------------------------------------------------------------
generate

if (SCR1_BRKM_PKG_BRKPT_NUMBER > 1)
begin : gen_csr_brkmctrl

always_comb begin
    logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1 : 0]     bp_matched;

    csr_brkmctrl_wr     = csr_brkmctrl_sel & csr_wr;
    csr_brkmctrl_in     = csr_wr_data;
    //
    for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
        bp_matched[i] = csr_bpcontrol_invrnt_reg[i].matched;
    end
    //
    csr_brkmctrl_out    = '0;
    if (csr_brkmctrl_sel) begin
        csr_brkmctrl_out.mode       = csr_brkmctrl_reg.mode;
        csr_brkmctrl_out.bp_i_skip  = csr_brkmctrl_reg.bp_i_skip;
        csr_brkmctrl_out.matched    = |bp_matched;
        csr_brkmctrl_out.init       = csr_brkmctrl_reg.init;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_brkmctrl_reg    <= '0;
    end
    else begin
        if (clk_en) begin
            csr_brkmctrl_reg.init           <= 1'b0;
            if (csr_brkmctrl_wr) begin
                csr_brkmctrl_reg.bp_i_skip  <= csr_brkmctrl_in.bp_i_skip;
                csr_brkmctrl_reg.init       <= csr_brkmctrl_in.init;
                csr_brkmctrl_reg.mode       <= csr_brkmctrl_in.mode;
            end
        end
    end
end

end : gen_csr_brkmctrl
else // (SCR1_BRKM_PKG_BRKPT_NUMBER == 1)
begin : gen_csr_brkmctrl

always_comb begin
    csr_brkmctrl_wr     = csr_brkmctrl_sel & csr_wr;
    csr_brkmctrl_in     = csr_wr_data;
    //
    csr_brkmctrl_out    = '0;
    if (csr_brkmctrl_sel) begin
        csr_brkmctrl_out.mode       = csr_brkmctrl_reg.mode;
        csr_brkmctrl_out.bp_i_skip  = csr_brkmctrl_reg.bp_i_skip;
        csr_brkmctrl_out.matched    = csr_bpcontrol_invrnt_reg[0].matched;
        csr_brkmctrl_out.init       = csr_brkmctrl_reg.init;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_brkmctrl_reg    <= '0;
    end
    else begin
        if (clk_en) begin
            csr_brkmctrl_reg.init           <= 1'b0;
            if (csr_brkmctrl_wr) begin
                csr_brkmctrl_reg.bp_i_skip  <= csr_brkmctrl_in.bp_i_skip;
                csr_brkmctrl_reg.init       <= csr_brkmctrl_in.init;
                csr_brkmctrl_reg.mode       <= csr_brkmctrl_in.mode;
            end
        end
    end
end

end : gen_csr_brkmctrl

endgenerate

//-------------------------------------------------------------------------------
// Matcher Array
//-------------------------------------------------------------------------------

generate

for (bp = 0; $unsigned(bp) < SCR1_BRKM_PKG_BRKPT_NUMBER; ++bp)
begin : gen_matcher_array
    if (BRKM_LCL_WATCH_EXEC)
    begin : gen_marray_watch_exec
        assign ma_i_valid[bp]   = bpmngt_bp_en[bp]
                                & exu2brkm_i_mon.vd
                                & csr_bpcontrol_execen_reg[bp];
        scr1_brkm_matcher #(
            .BRKM_MATCH_OPWIDTH_MAX         (BRKM_CFG_EXEC_OPWIDTH_MAX),
            .BRKM_MATCH_ADDR_EXACT          (BRKM_CFG_SUPP_ADDR_EXACT),
            .BRKM_MATCH_ADDR_MASK           (BRKM_CFG_SUPP_ADDR_MASK),
            .BRKM_MATCH_ADDR_MASK_EXT       (BRKM_CFG_SUPP_ADDR_MASK_EXT_EXEC),
            .BRKM_MATCH_ADDR_WIDTH          ((BRKM_LCL_WATCH_ADDR) ? BRKM_CFG_EXEC_ADDR_WIDTH : 1)
        )
        i_brkm_matcher_exec (
            // Common signals
            .valid                          (ma_i_valid[bp]),
            .width                          (exu2brkm_i_mon.width),
            // Address Channel
            .addr_exact_en                  (csr_bpcontrol_aen_reg[bp]),
            .addr_mask_en                   (csr_bpcontrol_amasken_reg[bp]),
            .addr_mask_ext_en               (csr_bpctrlext_amasken_reg[bp]),
            .addr                           (exu2brkm_i_mon.addr),
            .addr_lo                        (csr_bploaddr_reg[bp]),
            .addr_hi                        (csr_bphiaddr_reg[bp]),
            // Result
            .match                          (ma_i_match[bp])
        );
    end : gen_marray_watch_exec
    else
    begin : gen_marray_watch_exec
        assign ma_i_valid[bp] = 1'b0;
        assign ma_i_match[bp] = 1'b0;
    end : gen_marray_watch_exec

    if (BRKM_LCL_WATCH_LDST)
    begin : gen_marray_watch_ldst
        assign ma_d_valid[bp]   = bpmngt_bp_en[bp]
                                & lsu2brkm_d_mon.vd
                                & (   (csr_bpcontrol_loaden_reg [bp] & lsu2brkm_d_mon.load)
                                    | (csr_bpcontrol_storeen_reg[bp] & lsu2brkm_d_mon.store));
        scr1_brkm_matcher #(
            .BRKM_MATCH_OPWIDTH_MAX         (BRKM_CFG_LDST_OPWIDTH_MAX),
            .BRKM_MATCH_ADDR_EXACT          (BRKM_CFG_SUPP_ADDR_EXACT),
            .BRKM_MATCH_ADDR_MASK           (BRKM_CFG_SUPP_ADDR_MASK),
            .BRKM_MATCH_ADDR_MASK_EXT       (BRKM_CFG_SUPP_ADDR_MASK_EXT_LDST),
            .BRKM_MATCH_ADDR_WIDTH          ((BRKM_LCL_WATCH_ADDR) ? BRKM_CFG_LDST_ADDR_WIDTH : 1)
        )
        i_brkm_matcher_ldst (
            // Common signals
            .valid                          (ma_d_valid[bp]),
            .width                          (lsu2brkm_d_mon.width),
            // Address Channel
            .addr_exact_en                  (csr_bpcontrol_aen_reg[bp]),
            .addr_mask_en                   (csr_bpcontrol_amasken_reg[bp]),
            .addr_mask_ext_en               (csr_bpctrlext_amasken_reg[bp]),
            .addr                           (lsu2brkm_d_mon.addr),
            .addr_lo                        (csr_bploaddr_reg[bp]),
            .addr_hi                        (csr_bphiaddr_reg[bp]),
            // Result
            .match                          (ma_d_match[bp])
        );
    end : gen_marray_watch_ldst
    else
    begin : gen_marray_watch_ldst
        assign ma_d_valid[bp] = 1'b0;
        assign ma_d_match[bp] = 1'b0;
    end : gen_marray_watch_ldst
end : gen_matcher_array

endgenerate

//-------------------------------------------------------------------------------
// EXEC output
//-------------------------------------------------------------------------------

generate

if (BRKM_LCL_WATCH_EXEC)
begin : gen_exec_watch
    always_comb begin
        logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0] i_x_enbl;
        i_x_enbl            = '0;
        brkm2exu_i_match    = '0;
        bpmngt_bp_i_match   = 1'b0;
        brkm2exu_i_x_req    = 1'b0;
        brkm2lsu_i_x_req    = 1'b0;
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            brkm2exu_i_match[i] = ma_i_match[i];
            case (csr_bpcontrol_invrnt_reg[i].action)
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DBGEXC,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DMODE : begin
                    i_x_enbl[i] = 1'b1;
                end

                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_NONE,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_START,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_STOP,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_PACKT : begin
                    i_x_enbl[i] = 1'b0;
                end

                default : begin
                    i_x_enbl[i] = 1'bX;
                end
            endcase
            brkm2exu_i_x_req    |= i_x_enbl[i] & ma_i_match[i] & (~csr_bpctrlext_reg[i].dry_run);
            bpmngt_bp_i_match   |= i_x_enbl[i] & ma_i_match[i];
        end
        brkm2exu_i_x_req = (~ibpskip_state_reg) ? brkm2exu_i_x_req : 1'b0;
        brkm2lsu_i_x_req = brkm2exu_i_x_req;
    end
end : gen_exec_watch
else
begin : gen_exec_watch
    always_comb begin
        brkm2exu_i_match = '0;
        brkm2exu_i_x_req = 1'b0;
        brkm2lsu_i_x_req = 1'b0;
    end
end : gen_exec_watch

endgenerate

//-------------------------------------------------------------------------------
// LD/ST output
//-------------------------------------------------------------------------------

generate

if (BRKM_LCL_WATCH_LDST)
begin : gen_ldst_watch
    always_comb begin
        logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1 : 0] d_x_enbl;
        d_x_enbl         = '0;
        brkm2lsu_d_match = '0;
        brkm2lsu_d_x_req = 1'b0;
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            brkm2lsu_d_match[i] = ma_d_match[i];
        end
        for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
            brkm2lsu_d_match[i] = ma_d_match[i];
            case (csr_bpcontrol_invrnt_reg[i].action)
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DBGEXC,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DMODE : begin
                    d_x_enbl[i] = 1'b1;
                end

                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_NONE,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_START,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_STOP,
                SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_PACKT : begin
                    d_x_enbl[i] = 1'b0;
                end

                default : begin
                    d_x_enbl[i] = 1'bX;
                end
            endcase
            brkm2lsu_d_x_req |= d_x_enbl[i] & ma_d_match[i] & (~csr_bpctrlext_reg[i].dry_run);
        end
    end
end : gen_ldst_watch
else
begin : gen_ldst_watch
    always_comb begin
        brkm2lsu_d_match = '0;
        brkm2lsu_d_x_req = 1'b0;
    end
end : gen_ldst_watch

endgenerate

//-------------------------------------------------------------------------------
// Instruction Breakpoint (iBP) Skip logic
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ibpskip_state_reg    <= 1'b0;
    end
    else begin
        if (clk_en) begin
            if (  (bpmngt_init)
                | (exu2brkm_bp_i_recover)
            ) begin
                ibpskip_state_reg    <= csr_brkmctrl_reg.bp_i_skip;
            end
            else if (bpmngt_bp_i_match) begin
                ibpskip_state_reg    <= 1'b0;
            end
        end
    end
end

//-------------------------------------------------------------------------------
// Breakpoint Management logic
//-------------------------------------------------------------------------------
assign bpmngt_init = init | csr_brkmctrl_reg.init;
assign lsu_brk_en  = |bpmngt_bp_en;

always_comb begin
    logic [SCR1_BRKM_PKG_BRKPT_NUMBER-1:0] dmode_enbl;
    dmode_enbl              = '0;
    bpmngt_bp_en            = '0;
    bpmngt_bp_matched_set   = '0;
    brkm2dbga_dmode_req     = 1'b0;
    for (int unsigned i = 0; i < SCR1_BRKM_PKG_BRKPT_NUMBER; ++i) begin
        case (csr_bpcontrol_invrnt_reg[i].action)
            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_NONE : begin
                bpmngt_bp_en[i]          =  csr_bpctrlext_reg[i].dry_run & (~dsbl);
                bpmngt_bp_matched_set[i] =  csr_bpctrlext_reg[i].dry_run &
                                            exu2brkm_bp_retire[i];
            end

            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DBGEXC : begin
                bpmngt_bp_en[i]          = (~dsbl);
                bpmngt_bp_matched_set[i] = exu2brkm_bp_retire[i];
            end

            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DMODE : begin
                bpmngt_bp_en[i]          = (~dsbl);
                bpmngt_bp_matched_set[i] = exu2brkm_bp_retire[i];
                dmode_enbl[i]            = 1'b1;
            end

            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_START,
            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_STOP,
            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_PACKT,
            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_RSRV0,
            SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_RSRV1 : begin
                bpmngt_bp_en[i]          = 1'b0;
                bpmngt_bp_matched_set[i] = 1'b0;
            end

            default : begin
                bpmngt_bp_en[i]          = 1'bX;
                bpmngt_bp_matched_set[i] = 1'bX;
                dmode_enbl[i]            = 1'bX;
            end
        endcase
        brkm2dbga_dmode_req |= dmode_enbl[i] & exu2brkm_bp_retire[i];
    end
end

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_BRKM_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({
        init,
        dsbl,
        csr2brkm_req,
        exu2brkm_i_mon.vd,
        lsu2brkm_d_mon.vd,
        exu2brkm_bp_retire,
        exu2brkm_bp_i_recover
    })
) else
    $error("BRKM error: unknown values");

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_brkm

`endif // SCR1_BRKM_EN
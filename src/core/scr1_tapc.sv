/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_tapc.sv>
/// @brief      TAP Controller (TAPC)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_tapc.svh"
`include "scr1_dbgc.svh"

module scr1_tapc (
    // JTAG signals
    input   logic                                   trst_n,         // Test Reset (TRSTn)
    input   logic                                   tck,            // Test Clock (TCK)
    input   logic                                   tms,            // Test Mode Select (TMS)
    input   logic                                   tdi,            // Test Data Input (TDI)
    output  logic                                   tdo,            // Test Data Output (TDO)
    output  logic                                   tdo_en,         // TDO Enable, signal for TDO buffer control
    // System Control/Status signals
    output  logic                                   sys_rst_ctrl,   // System Reset Control
    input   logic                                   sys_rst_sts,    // System Reset Status
    // Master TAP Select signal
    output  logic                                   master_tap_sel, // Master TAP Select
    // DAP scan-chains
    output  logic                                   dap_ch_sel,     // DAP Chain Select
    output  logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]   dap_ch_id,      // DAP Chain Identificator
    output  logic                                   dap_ch_capture, // DAP Chain Capture
    output  logic                                   dap_ch_shift,   // DAP Chain Shift
    output  logic                                   dap_ch_update,  // DAP Chain Update
    output  logic                                   dap_ch_tdi,     // DAP Chain TDI
    input   logic                                   dap_ch_tdo      // DAP Chain TDO
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

logic trst_n_int;

logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_reg;         // Instruction Register (IR)
logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_next;
logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_shift_reg;   // Instruction Register, shift part

type_scr1_tap_state_e                       tap_state_reg;      // TAP's current state
type_scr1_tap_state_e                       tap_state_next;     // TAP's next state

logic                                       dr_out;
logic                                       dr_bypass_sel;      // BYPASS register selector
logic                                       dr_idcode_sel;      // IDCODE register selector

logic                                       dr_bld_id_sel;
logic [SCR1_TAP_DR_BLD_ID_WIDTH-1:0]        dr_bld_id_reg_nc;
logic [SCR1_TAP_DR_IDCODE_WIDTH-1:0]        dr_idcode_reg_nc;
logic                                       dr_bypass_reg_nc;

logic                                       dr_bld_id_tdo;
logic                                       dr_bypass_tdo;
logic                                       dr_idcode_tdo;

logic                                       dr_sys_ctrl_sel;
logic [SCR1_TAP_DR_SYS_CTRL_WIDTH-1:0]      dr_sys_ctrl_pdin;
logic [SCR1_TAP_DR_SYS_CTRL_WIDTH-1:0]      dr_sys_ctrl_pdout;
logic                                       dr_sys_ctrl_tdo;

logic                                       dr_mtap_switch_sel;
logic [SCR1_TAP_DR_MTAP_SWITCH_WIDTH-1:0]   dr_mtap_switch_pdin;
logic [SCR1_TAP_DR_MTAP_SWITCH_WIDTH-1:0]   dr_mtap_switch_pdout;
logic                                       dr_mtap_switch_tdo;

logic                                       tap_fsm_ir_shift;
logic                                       tap_fsm_dr_capture;
logic                                       tap_fsm_dr_shift;
logic                                       tap_fsm_dr_update;

logic                                       tdo_mux_out;
logic                                       tdo_mux_out_reg;
logic                                       tdo_mux_en;
logic                                       tdo_mux_en_reg;

//-------------------------------------------------------------------------------
// Reset logic
//-------------------------------------------------------------------------------

always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        trst_n_int <= 1'b0;
    end
    else begin
        if (tap_state_reg == SCR1_TAP_STATE_RESET) begin
            trst_n_int <= 1'b0;
        end
        else begin
            trst_n_int <= 1'b1;
        end
    end
end

//-------------------------------------------------------------------------------
// TAP's FSM
//-------------------------------------------------------------------------------
always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_state_reg <= SCR1_TAP_STATE_RESET;
    end
    else begin
        tap_state_reg <= tap_state_next;
    end
end

always_comb begin
    case (tap_state_reg)
        SCR1_TAP_STATE_RESET        : tap_state_next = tms ? SCR1_TAP_STATE_RESET        : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_IDLE         : tap_state_next = tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_DR_SEL_SCAN  : tap_state_next = tms ? SCR1_TAP_STATE_IR_SEL_SCAN  : SCR1_TAP_STATE_DR_CAPTURE;
        SCR1_TAP_STATE_DR_CAPTURE   : tap_state_next = tms ? SCR1_TAP_STATE_DR_EXIT1     : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_SHIFT     : tap_state_next = tms ? SCR1_TAP_STATE_DR_EXIT1     : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_EXIT1     : tap_state_next = tms ? SCR1_TAP_STATE_DR_UPDATE    : SCR1_TAP_STATE_DR_PAUSE;
        SCR1_TAP_STATE_DR_PAUSE     : tap_state_next = tms ? SCR1_TAP_STATE_DR_EXIT2     : SCR1_TAP_STATE_DR_PAUSE;
        SCR1_TAP_STATE_DR_EXIT2     : tap_state_next = tms ? SCR1_TAP_STATE_DR_UPDATE    : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_UPDATE    : tap_state_next = tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_IR_SEL_SCAN  : tap_state_next = tms ? SCR1_TAP_STATE_RESET        : SCR1_TAP_STATE_IR_CAPTURE;
        SCR1_TAP_STATE_IR_CAPTURE   : tap_state_next = tms ? SCR1_TAP_STATE_IR_EXIT1     : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_SHIFT     : tap_state_next = tms ? SCR1_TAP_STATE_IR_EXIT1     : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_EXIT1     : tap_state_next = tms ? SCR1_TAP_STATE_IR_UPDATE    : SCR1_TAP_STATE_IR_PAUSE;
        SCR1_TAP_STATE_IR_PAUSE     : tap_state_next = tms ? SCR1_TAP_STATE_IR_EXIT2     : SCR1_TAP_STATE_IR_PAUSE;
        SCR1_TAP_STATE_IR_EXIT2     : tap_state_next = tms ? SCR1_TAP_STATE_IR_UPDATE    : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_UPDATE    : tap_state_next = tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
        default                     : tap_state_next = SCR1_TAP_STATE_XXX;
    endcase
end

//-------------------------------------------------------------------------------
// Instruction Register (IR)
//-------------------------------------------------------------------------------
always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_ir_reg <= SCR1_TAP_INSTR_IDCODE;
    end
    else if (~trst_n_int) begin
        tap_ir_reg <= SCR1_TAP_INSTR_IDCODE;
    end
    else begin
        tap_ir_reg <= tap_ir_next;
    end
end

always_comb begin
    case (tap_state_reg)
        SCR1_TAP_STATE_IR_UPDATE    : tap_ir_next = tap_ir_shift_reg;
        default                     : tap_ir_next = tap_ir_reg;
    endcase
end

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_ir_shift_reg <= '0;
    end
    else if (~trst_n_int) begin
        tap_ir_shift_reg <= '0;
    end
    else begin
        case (tap_state_reg)
            SCR1_TAP_STATE_IR_CAPTURE :
                tap_ir_shift_reg <= {{($bits(tap_ir_shift_reg)-1){1'b0}}, 1'b1};
            SCR1_TAP_STATE_IR_SHIFT :
                tap_ir_shift_reg <= {tdi, tap_ir_shift_reg[$left(tap_ir_shift_reg):1]};
            default : begin
                    // Just store previous value
                end
        endcase
    end
end

//-------------------------------------------------------------------------------
// Control signals
//-------------------------------------------------------------------------------
always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_fsm_ir_shift <= 1'b0;
    end
    else if (~trst_n_int) begin
        tap_fsm_ir_shift <= 1'b0;
    end
    else begin
        if (  (   (tap_state_reg == SCR1_TAP_STATE_IR_CAPTURE)
                | (tap_state_reg == SCR1_TAP_STATE_IR_SHIFT)
                | (tap_state_reg == SCR1_TAP_STATE_IR_EXIT2)   )
            & (~tms)
        ) begin
            tap_fsm_ir_shift <= 1'b1;
        end
        else begin
            if (tap_fsm_ir_shift) begin
                tap_fsm_ir_shift <= 1'b0;
            end
        end
    end
end

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_fsm_dr_capture <= 1'b0;
    end
    else if (~trst_n_int) begin
        tap_fsm_dr_capture <= 1'b0;
    end
    else begin
        if (  (tap_state_reg == SCR1_TAP_STATE_DR_SEL_SCAN)
            & (~tms)
        ) begin
            tap_fsm_dr_capture <= 1'b1;
        end
        else begin
            if (tap_fsm_dr_capture) begin
                tap_fsm_dr_capture <= 1'b0;
            end
        end
    end
end

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_fsm_dr_shift <= 1'b0;
    end
    else if (~trst_n_int) begin
        tap_fsm_dr_shift <= 1'b0;
    end
    else begin
        if ( (    (tap_state_reg == SCR1_TAP_STATE_DR_CAPTURE)
                | (tap_state_reg == SCR1_TAP_STATE_DR_SHIFT)
                | (tap_state_reg == SCR1_TAP_STATE_DR_EXIT2)   )
            & (~tms)
        ) begin
            tap_fsm_dr_shift <= 1'b1;
        end
        else begin
            if (tap_fsm_dr_shift) begin
                tap_fsm_dr_shift <= 1'b0;
            end
        end
    end
end

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tap_fsm_dr_update <= 1'b0;
    end
    else if (~trst_n_int) begin
        tap_fsm_dr_update <= 1'b0;
    end
    else begin
        if (  (   (tap_state_reg == SCR1_TAP_STATE_DR_EXIT1)
                | (tap_state_reg == SCR1_TAP_STATE_DR_EXIT2) )
            & (tms)
        ) begin
            tap_fsm_dr_update <= 1'b1;
        end
        else begin
            if (tap_fsm_dr_update) begin
                tap_fsm_dr_update <= 1'b0;
            end
        end
    end
end

//-------------------------------------------------------------------------------
// IR Decoder / DR Outputs Multiplexor
//-------------------------------------------------------------------------------
always_comb begin
    dr_out                          = 1'b0;
    dr_bypass_sel                   = 1'b0;
    dr_idcode_sel                   = 1'b0;
    dr_bld_id_sel                   = 1'b0;
    dr_sys_ctrl_sel                 = 1'b0;
    dr_mtap_switch_sel              = 1'b0;
    dap_ch_sel                      = 1'b0;
    dap_ch_id                       = '0;
    case (tap_ir_reg)
        SCR1_TAP_INSTR_IDCODE : begin
            dr_idcode_sel           = 1'b1;
            dr_out                  = dr_idcode_tdo;
        end
        SCR1_TAP_INSTR_BYPASS : begin
            dr_bypass_sel           = 1'b1;
            dr_out                  = dr_bypass_tdo;
        end
        SCR1_TAP_INSTR_DBG_ID : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DBG_ID;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_BLD_ID : begin
            dr_bld_id_sel           = 1'b1;
            dr_out                  = dr_bld_id_tdo;
        end
        SCR1_TAP_INSTR_SYS_CTRL : begin
            dr_sys_ctrl_sel         = 1'b1;
            dr_out                  = dr_sys_ctrl_tdo;
        end
        SCR1_TAP_INSTR_MTAP_SWITCH : begin
            dr_mtap_switch_sel      = 1'b1;
            dr_out                  = dr_mtap_switch_tdo;
        end
        SCR1_TAP_INSTR_DBG_STATUS : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DBG_STATUS;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_DAP_CTRL : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DAP_CTRL;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_DAP_CTRL_RD : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DAP_CTRL_RD;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_DAP_CMD : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DAP_CMD;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_PIPELN_STS : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_DBG_PIPE_STS;
            dr_out                  = dap_ch_tdo;
        end
        SCR1_TAP_INSTR_TARGET_ID : begin
            dap_ch_sel              = 1'b1;
            dap_ch_id               = SCR1_DAP_CHAIN_ID_TARGET_ID;
            dr_out                  = dap_ch_tdo;
        end
        default : begin
            dr_bypass_sel           = 1'b1;
            dr_out                  = dr_bypass_tdo;
        end
    endcase
end

//-------------------------------------------------------------------------------
// TDO Multiplexor & Output Registers
//-------------------------------------------------------------------------------
always_comb begin
    tdo_mux_en = 1'b0;
    tdo_mux_out     = 1'b0;
    if (tap_fsm_dr_shift) begin
        tdo_mux_en  = 1'b1;
        tdo_mux_out = dr_out;
    end else if (tap_fsm_ir_shift) begin
        tdo_mux_en  = 1'b1;
        tdo_mux_out = tap_ir_shift_reg[0];
    end
end

always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tdo_mux_out_reg <= 1'b0;
        tdo_mux_en_reg  <= 1'b0;
    end
    else if (~trst_n_int) begin
        tdo_mux_out_reg <= 1'b0;
        tdo_mux_en_reg  <= 1'b0;
    end
    else begin
        tdo_mux_out_reg <= tdo_mux_out;
        tdo_mux_en_reg  <= tdo_mux_en;
    end
end

assign tdo      = tdo_mux_out_reg;
assign tdo_en   = tdo_mux_en_reg;

//-------------------------------------------------------------------------------
// DR :: BYPASS register
//-------------------------------------------------------------------------------

scr1_tapc_shift_reg #(
        .SCR1_WIDTH         (SCR1_TAP_DR_BYPASS_WIDTH),
        .SCR1_RESET_VALUE   (SCR1_TAP_DR_BYPASS_WIDTH'(0))
    )
    i_bypass_reg(
        .clk                (tck),
        .rst_n              (trst_n),
        .rst_n_sync         (trst_n_int),
        .fsm_dr_select      (dr_bypass_sel),
        .fsm_dr_capture     (tap_fsm_dr_capture),
        .fsm_dr_shift       (tap_fsm_dr_shift),
        .din_serial         (tdi),
        .din_parallel       (1'b0),
        .dout_serial        (dr_bypass_tdo),
        .dout_parallel      (dr_bypass_reg_nc)
);

//-------------------------------------------------------------------------------
// DR :: IDCODE register
//-------------------------------------------------------------------------------

scr1_tapc_shift_reg #(
        .SCR1_WIDTH         (SCR1_TAP_DR_IDCODE_WIDTH),
        .SCR1_RESET_VALUE   (SCR1_TAP_DR_IDCODE_WIDTH'(SCR1_TAP_IDCODE_RISCV_SC))
    )
    i_tap_idcode_reg(
        .clk                (tck),
        .rst_n              (trst_n),
        .rst_n_sync         (trst_n_int),
        .fsm_dr_select      (dr_idcode_sel),
        .fsm_dr_capture     (tap_fsm_dr_capture),
        .fsm_dr_shift       (tap_fsm_dr_shift),
        .din_serial         (tdi),
        .din_parallel       (SCR1_TAP_IDCODE_RISCV_SC),
        .dout_serial        (dr_idcode_tdo),
        .dout_parallel      (dr_idcode_reg_nc)
);

//-------------------------------------------------------------------------------
// DR :: DBG_ID register
//-------------------------------------------------------------------------------

//-------------------------------------------------------------------------------
// DR :: BLD_ID register
//-------------------------------------------------------------------------------
scr1_tapc_shift_reg #(
        .SCR1_WIDTH         (SCR1_TAP_DR_DBG_ID_WIDTH),
        .SCR1_RESET_VALUE   (SCR1_TAP_DR_DBG_ID_WIDTH'(0))
    )
    i_tap_dr_bld_id_reg(
        .clk                (tck),
        .rst_n              (trst_n),
        .rst_n_sync         (trst_n_int),
        .fsm_dr_select      (dr_bld_id_sel),
        .fsm_dr_capture     (tap_fsm_dr_capture),
        .fsm_dr_shift       (tap_fsm_dr_shift),
        .din_serial         (tdi),
        .din_parallel       (SCR1_TAP_BLD_ID_VALUE),
        .dout_serial        (dr_bld_id_tdo),
        .dout_parallel      (dr_bld_id_reg_nc)
);

//-------------------------------------------------------------------------------
// DR :: SYS_CTRL register
//-------------------------------------------------------------------------------
scr1_tapc_data_reg #(
        .SCR1_WIDTH         (SCR1_TAP_DR_SYS_CTRL_WIDTH),
        .SCR1_RESET_VALUE   (SCR1_TAP_DR_SYS_CTRL_WIDTH'(0))
    )
    i_tap_dr_sys_ctrl_reg(
        .clk                (tck),
        .rst_n              (trst_n),
        .rst_n_sync         (trst_n_int),
        .fsm_dr_select      (dr_sys_ctrl_sel),
        .fsm_dr_capture     (tap_fsm_dr_capture),
        .fsm_dr_shift       (tap_fsm_dr_shift),
        .fsm_dr_update      (tap_fsm_dr_update),
        .din_serial         (tdi),
        .din_parallel       (dr_sys_ctrl_pdin),
        .dout_serial        (dr_sys_ctrl_tdo),
        .dout_parallel      (dr_sys_ctrl_pdout)
);
assign dr_sys_ctrl_pdin[0]  = sys_rst_sts;
assign sys_rst_ctrl         = dr_sys_ctrl_pdout[0];

//-------------------------------------------------------------------------------
// DR :: MTAP_SWITCH register (Master TAP Switch)
//-------------------------------------------------------------------------------
scr1_tapc_data_reg #(
        .SCR1_WIDTH         (SCR1_TAP_DR_MTAP_SWITCH_WIDTH),
        .SCR1_RESET_VALUE   (SCR1_TAP_DR_MTAP_SWITCH_WIDTH'(0))
    )
    i_tap_dr_mtap_switch_reg(
        .clk                (tck),
        .rst_n              (trst_n),
        .rst_n_sync         (trst_n_int),
        .fsm_dr_select      (dr_mtap_switch_sel),
        .fsm_dr_capture     (tap_fsm_dr_capture),
        .fsm_dr_shift       (tap_fsm_dr_shift),
        .fsm_dr_update      (tap_fsm_dr_update),
        .din_serial         (tdi),
        .din_parallel       (dr_mtap_switch_pdin),
        .dout_serial        (dr_mtap_switch_tdo),
        .dout_parallel      (dr_mtap_switch_pdout)
);
assign dr_mtap_switch_pdin[0] = dr_mtap_switch_pdout[0];
assign master_tap_sel         = dr_mtap_switch_pdout[0];

//-------------------------------------------------------------------------------
// DR :: DAP Scan Chains
//-------------------------------------------------------------------------------
assign dap_ch_tdi       = tdi;
assign dap_ch_capture   = tap_fsm_dr_capture;
assign dap_ch_shift     = tap_fsm_dr_shift;
assign dap_ch_update    = tap_fsm_dr_update;

// Misc


`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_TAPC_XCHECK : assert property (
    @(posedge tck) disable iff (~trst_n)
    !$isunknown({
        tms,
        tdi,
        sys_rst_sts
    })
) else begin
    $error("TAPC error: unknown values");
end

SCR1_SVA_TAPC_XCHECK_NEGCLK : assert property (
    @(negedge tck) disable iff (~trst_n)
    !$isunknown({
        dap_ch_tdo
    })
) else begin
    $error("TAPC @negedge error: unknown values");
end

`endif // SCR1_SIM_ENV

endmodule : scr1_tapc

`endif // SCR1_DBGC_EN
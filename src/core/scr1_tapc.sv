/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_tapc.sv>
/// @brief      TAP Controller (TAPC)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Controls TAP operation
 // - Allows debugger to access TAP Data registers and DMI/SCU scan-chains via
 //   command written in Instruction register
 //
 // Structure:
 // - Synchronous reset generation
 // - TAPC FSM
 // - TAPC Instruction Registers
 // - TAPC DRs/DMI/SCU scan-chains
 // - TAPC TDO enable and output Registers
 // - TAPC Data Registers
 //   - BYPASS
 //   - IDCODE
 //   - BUILD ID
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN
`include "scr1_tapc.svh"
`include "scr1_dm.svh"

module scr1_tapc (
    // JTAG signals
    input   logic                                   tapc_trst_n,                    // Test Reset (TRSTn)
    input   logic                                   tapc_tck,                       // Test Clock (TCK)
    input   logic                                   tapc_tms,                       // Test Mode Select (TMS)
    input   logic                                   tapc_tdi,                       // Test Data Input (TDI)
    output  logic                                   tapc_tdo,                       // Test Data Output (TDO)
    output  logic                                   tapc_tdo_en,                    // TDO Enable, signal for TDO buffer control

    // Fuses:
    input   logic [31:0]                            soc2tapc_fuse_idcode_i,         // IDCODE value from fuses

    // DMI/SCU scan-chains
    output  logic                                   tapc2tapcsync_scu_ch_sel_o,     // SCU Chain Select
    output  logic                                   tapc2tapcsync_dmi_ch_sel_o,     // DMI Chain Select
    output  logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]    tapc2tapcsync_ch_id_o,          // DMI/SCU Chain Identifier
    output  logic                                   tapc2tapcsync_ch_capture_o,     // DMI/SCU Chain Capture
    output  logic                                   tapc2tapcsync_ch_shift_o,       // DMI/SCU Chain Shift
    output  logic                                   tapc2tapcsync_ch_update_o,      // DMI/SCU Chain Update
    output  logic                                   tapc2tapcsync_ch_tdi_o,         // DMI/SCU Chain TDI
    input   logic                                   tapcsync2tapc_ch_tdo_i          // DMI/SCU Chain TDO
);

//------------------------------------------------------------------------------
// Local Signals
//------------------------------------------------------------------------------

logic                                       trst_n_int;       // Sync reset signal

// TAPC FSM signals
//------------------------------------------------------------------------------

type_scr1_tap_state_e                       tap_fsm_ff;       // TAP's current state
type_scr1_tap_state_e                       tap_fsm_next;     // TAP's next state

// Control signals
logic                                       tap_fsm_reset;
logic                                       tap_fsm_ir_upd;
logic                                       tap_fsm_ir_cap;
logic                                       tap_fsm_ir_shft;

// Registered control signals
logic                                       tap_fsm_ir_shift_ff;
logic                                       tap_fsm_ir_shift_next;
logic                                       tap_fsm_dr_capture_ff;
logic                                       tap_fsm_dr_capture_next;
logic                                       tap_fsm_dr_shift_ff;
logic                                       tap_fsm_dr_shift_next;
logic                                       tap_fsm_dr_update_ff;
logic                                       tap_fsm_dr_update_next;

// TAPC Instruction Registers signals
//------------------------------------------------------------------------------

logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_shift_ff;   // Instruction Shift Register
logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_shift_next; // Instruction Shift Register next value
logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_ff;         // Instruction Register
logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0]      tap_ir_next;       // Instruction Register next value

// TAPC Data Registers signals
//------------------------------------------------------------------------------

// BYPASS register
logic                                       dr_bypass_sel;
logic                                       dr_bypass_tdo;

// IDCODE register
logic                                       dr_idcode_sel;
logic                                       dr_idcode_tdo;

// BUILD ID register
logic                                       dr_bld_id_sel;
logic                                       dr_bld_id_tdo;

logic                                       dr_out;

// TDO registers
//------------------------------------------------------------------------------

// TDO enable register
logic                                       tdo_en_ff;
logic                                       tdo_en_next;

// TDO output register
logic                                       tdo_out_ff;
logic                                       tdo_out_next;

//------------------------------------------------------------------------------
// TAPC Synchronous Reset logic
//------------------------------------------------------------------------------

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        trst_n_int <= 1'b0;
    end else begin
        trst_n_int <= ~tap_fsm_reset;
    end
end

//------------------------------------------------------------------------------
// TAP's FSM
//------------------------------------------------------------------------------

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_fsm_ff <= SCR1_TAP_STATE_RESET;
    end else begin
        tap_fsm_ff <= tap_fsm_next;
    end
end

always_comb begin
    case (tap_fsm_ff)
        SCR1_TAP_STATE_RESET      : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_RESET        : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_IDLE       : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_DR_SEL_SCAN: tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_SEL_SCAN  : SCR1_TAP_STATE_DR_CAPTURE;
        SCR1_TAP_STATE_DR_CAPTURE : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_EXIT1     : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_SHIFT   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_EXIT1     : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_EXIT1   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_UPDATE    : SCR1_TAP_STATE_DR_PAUSE;
        SCR1_TAP_STATE_DR_PAUSE   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_EXIT2     : SCR1_TAP_STATE_DR_PAUSE;
        SCR1_TAP_STATE_DR_EXIT2   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_UPDATE    : SCR1_TAP_STATE_DR_SHIFT;
        SCR1_TAP_STATE_DR_UPDATE  : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
        SCR1_TAP_STATE_IR_SEL_SCAN: tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_RESET        : SCR1_TAP_STATE_IR_CAPTURE;
        SCR1_TAP_STATE_IR_CAPTURE : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_EXIT1     : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_SHIFT   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_EXIT1     : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_EXIT1   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_UPDATE    : SCR1_TAP_STATE_IR_PAUSE;
        SCR1_TAP_STATE_IR_PAUSE   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_EXIT2     : SCR1_TAP_STATE_IR_PAUSE;
        SCR1_TAP_STATE_IR_EXIT2   : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_IR_UPDATE    : SCR1_TAP_STATE_IR_SHIFT;
        SCR1_TAP_STATE_IR_UPDATE  : tap_fsm_next = tapc_tms ? SCR1_TAP_STATE_DR_SEL_SCAN  : SCR1_TAP_STATE_IDLE;
`ifdef SCR1_XPROP_EN
        default                   : tap_fsm_next = SCR1_TAP_STATE_XXX;
`else // SCR1_XPROP_EN
        default                   : tap_fsm_next = tap_fsm_ff;
`endif // SCR1_XPROP_EN
    endcase
end

assign tap_fsm_reset   = (tap_fsm_ff == SCR1_TAP_STATE_RESET);
assign tap_fsm_ir_upd  = (tap_fsm_ff == SCR1_TAP_STATE_IR_UPDATE);
assign tap_fsm_ir_cap  = (tap_fsm_ff == SCR1_TAP_STATE_IR_CAPTURE);
assign tap_fsm_ir_shft = (tap_fsm_ff == SCR1_TAP_STATE_IR_SHIFT);

//------------------------------------------------------------------------------
// TAPC Instruction Registers
//------------------------------------------------------------------------------

// TAPC Instruction Shift register
//------------------------------------------------------------------------------

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_ir_shift_ff <= '0;
    end else if (~trst_n_int) begin
        tap_ir_shift_ff <= '0;
    end else begin
        tap_ir_shift_ff <= tap_ir_shift_next;
    end
end

assign tap_ir_shift_next = tap_fsm_ir_cap  ? {{($bits(tap_ir_shift_ff)-1){1'b0}}, 1'b1}
                         : tap_fsm_ir_shft ? {tapc_tdi, tap_ir_shift_ff[$left(tap_ir_shift_ff):1]}
                                           : tap_ir_shift_ff;

// TAPC Instruction register
//------------------------------------------------------------------------------

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_ir_ff <= SCR1_TAP_INSTR_IDCODE;
    end else if (~trst_n_int) begin
        tap_ir_ff <= SCR1_TAP_INSTR_IDCODE;
    end else begin
        tap_ir_ff <= tap_ir_next;
    end
end

assign tap_ir_next = tap_fsm_ir_upd ? tap_ir_shift_ff : tap_ir_ff;

//------------------------------------------------------------------------------
// Control signals
//------------------------------------------------------------------------------

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_fsm_ir_shift_ff <= 1'b0;
    end else if (~trst_n_int) begin
        tap_fsm_ir_shift_ff <= 1'b0;
    end else begin
        tap_fsm_ir_shift_ff <= tap_fsm_ir_shift_next;
    end
end

assign tap_fsm_ir_shift_next = (tap_fsm_next == SCR1_TAP_STATE_IR_SHIFT);

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_fsm_dr_capture_ff <= 1'b0;
    end else if (~trst_n_int) begin
        tap_fsm_dr_capture_ff <= 1'b0;
    end else begin
        tap_fsm_dr_capture_ff <= tap_fsm_dr_capture_next;
    end
end

assign tap_fsm_dr_capture_next = (tap_fsm_next == SCR1_TAP_STATE_DR_CAPTURE);

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_fsm_dr_shift_ff <= 1'b0;
    end else if (~trst_n_int) begin
        tap_fsm_dr_shift_ff <= 1'b0;
    end else begin
        tap_fsm_dr_shift_ff <= tap_fsm_dr_shift_next;
    end
end

assign tap_fsm_dr_shift_next = (tap_fsm_next == SCR1_TAP_STATE_DR_SHIFT);

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tap_fsm_dr_update_ff <= 1'b0;
    end else if (~trst_n_int) begin
        tap_fsm_dr_update_ff <= 1'b0;
    end else begin
        tap_fsm_dr_update_ff <= tap_fsm_dr_update_next;
    end
end

assign tap_fsm_dr_update_next = (tap_fsm_next == SCR1_TAP_STATE_DR_UPDATE);

//------------------------------------------------------------------------------
// TAPC DRs/DMI/SCU scan-chains
//------------------------------------------------------------------------------
//
 // Consists of the following functional units:
 // - Data source/destination decoder
 // - DMI channel ID decoder

// - Read data multiplexer
// Data source/destination decoder
//------------------------------------------------------------------------------

always_comb begin
    dr_bypass_sel               = 1'b0;
    dr_idcode_sel               = 1'b0;
    dr_bld_id_sel               = 1'b0;
    tapc2tapcsync_scu_ch_sel_o  = 1'b0;
    tapc2tapcsync_dmi_ch_sel_o  = 1'b0;
    case (tap_ir_ff)
        SCR1_TAP_INSTR_DTMCS     : tapc2tapcsync_dmi_ch_sel_o = 1'b1;
        SCR1_TAP_INSTR_DMI_ACCESS: tapc2tapcsync_dmi_ch_sel_o = 1'b1;
        SCR1_TAP_INSTR_IDCODE    : dr_idcode_sel              = 1'b1;
        SCR1_TAP_INSTR_BYPASS    : dr_bypass_sel              = 1'b1;
        SCR1_TAP_INSTR_BLD_ID    : dr_bld_id_sel              = 1'b1;
        SCR1_TAP_INSTR_SCU_ACCESS: tapc2tapcsync_scu_ch_sel_o = 1'b1;
        default                  : dr_bypass_sel              = 1'b1;
    endcase
end

// DMI channel ID decoder
//------------------------------------------------------------------------------

always_comb begin
    tapc2tapcsync_ch_id_o = '0;
    case (tap_ir_ff)
        SCR1_TAP_INSTR_DTMCS     : tapc2tapcsync_ch_id_o = 'd1;
        SCR1_TAP_INSTR_DMI_ACCESS: tapc2tapcsync_ch_id_o = 'd2;
        default                  : tapc2tapcsync_ch_id_o = '0;
    endcase
end

// Read data multiplexer
//------------------------------------------------------------------------------

always_comb begin
    dr_out = 1'b0;
    case (tap_ir_ff)
        SCR1_TAP_INSTR_DTMCS     : dr_out = tapcsync2tapc_ch_tdo_i;
        SCR1_TAP_INSTR_DMI_ACCESS: dr_out = tapcsync2tapc_ch_tdo_i;
        SCR1_TAP_INSTR_IDCODE    : dr_out = dr_idcode_tdo;
        SCR1_TAP_INSTR_BYPASS    : dr_out = dr_bypass_tdo;
        SCR1_TAP_INSTR_BLD_ID    : dr_out = dr_bld_id_tdo;
        SCR1_TAP_INSTR_SCU_ACCESS: dr_out = tapcsync2tapc_ch_tdo_i;
        default                  : dr_out = dr_bypass_tdo;
    endcase
end

//------------------------------------------------------------------------------
// TDO enable and output registers
//------------------------------------------------------------------------------

// TDO enable register
//------------------------------------------------------------------------------

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tdo_en_ff  <= 1'b0;
    end else if (~trst_n_int) begin
        tdo_en_ff  <= 1'b0;
    end else begin
        tdo_en_ff  <= tdo_en_next;
    end
end

assign tdo_en_next = tap_fsm_dr_shift_ff | tap_fsm_ir_shift_ff;

// TDO output register
//------------------------------------------------------------------------------

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tdo_out_ff <= 1'b0;
    end else if (~trst_n_int) begin
        tdo_out_ff <= 1'b0;
    end else begin
        tdo_out_ff <= tdo_out_next;
    end
end

assign tdo_out_next = tap_fsm_dr_shift_ff ? dr_out
                    : tap_fsm_ir_shift_ff ? tap_ir_shift_ff[0]
                                          : 1'b0;

// TAPC TDO signals
assign tapc_tdo_en = tdo_en_ff;
assign tapc_tdo    = tdo_out_ff;

//------------------------------------------------------------------------------
// TAPC Data Registers
//------------------------------------------------------------------------------
//
 // Registers:
 // - BYPASS register
 // - IDCODE register
 // - BUILD ID register

// BYPASS register
//------------------------------------------------------------------------------
// 1-bit mandatory IEEE 1149.1 compliant register

scr1_tapc_shift_reg  #(
    .SCR1_WIDTH       (SCR1_TAP_DR_BYPASS_WIDTH),
    .SCR1_RESET_VALUE (SCR1_TAP_DR_BYPASS_WIDTH'(0))
) i_bypass_reg        (
    .clk              (tapc_tck             ),
    .rst_n            (tapc_trst_n          ),
    .rst_n_sync       (trst_n_int           ),
    .fsm_dr_select    (dr_bypass_sel        ),
    .fsm_dr_capture   (tap_fsm_dr_capture_ff),
    .fsm_dr_shift     (tap_fsm_dr_shift_ff  ),
    .din_serial       (tapc_tdi             ),
    .din_parallel     (1'b0                 ),
    .dout_serial      (dr_bypass_tdo        ),
    .dout_parallel    (                     )
);

// IDCODE register
//------------------------------------------------------------------------------
// Holds the Device ID value (mandatory IEEE 1149.1 compliant register)

scr1_tapc_shift_reg  #(
    .SCR1_WIDTH       (SCR1_TAP_DR_IDCODE_WIDTH),
    .SCR1_RESET_VALUE (SCR1_TAP_DR_IDCODE_WIDTH'(0))
) i_tap_idcode_reg    (
    .clk              (tapc_tck              ),
    .rst_n            (tapc_trst_n           ),
    .rst_n_sync       (trst_n_int            ),
    .fsm_dr_select    (dr_idcode_sel         ),
    .fsm_dr_capture   (tap_fsm_dr_capture_ff ),
    .fsm_dr_shift     (tap_fsm_dr_shift_ff   ),
    .din_serial       (tapc_tdi              ),
    .din_parallel     (soc2tapc_fuse_idcode_i),
    .dout_serial      (dr_idcode_tdo         ),
    .dout_parallel    (                      )
);

// BUILD ID register
//------------------------------------------------------------------------------
// Holds the BUILD ID value

scr1_tapc_shift_reg  #(
    .SCR1_WIDTH       (SCR1_TAP_DR_BLD_ID_WIDTH),
    .SCR1_RESET_VALUE (SCR1_TAP_DR_BLD_ID_WIDTH'(0))
) i_tap_dr_bld_id_reg (
    .clk              (tapc_tck             ),
    .rst_n            (tapc_trst_n          ),
    .rst_n_sync       (trst_n_int           ),
    .fsm_dr_select    (dr_bld_id_sel        ),
    .fsm_dr_capture   (tap_fsm_dr_capture_ff),
    .fsm_dr_shift     (tap_fsm_dr_shift_ff  ),
    .din_serial       (tapc_tdi             ),
    .din_parallel     (SCR1_TAP_BLD_ID_VALUE),
    .dout_serial      (dr_bld_id_tdo        ),
    .dout_parallel    (                     )
);

//------------------------------------------------------------------------------
// DMI/SCU scan-chains signals
//------------------------------------------------------------------------------

assign tapc2tapcsync_ch_tdi_o     = tapc_tdi;
assign tapc2tapcsync_ch_capture_o = tap_fsm_dr_capture_ff;
assign tapc2tapcsync_ch_shift_o   = tap_fsm_dr_shift_ff;
assign tapc2tapcsync_ch_update_o  = tap_fsm_dr_update_ff;

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_TAPC_XCHECK : assert property (
    @(posedge tapc_tck) disable iff (~tapc_trst_n)
    !$isunknown({tapc_tms, tapc_tdi})
) else $error("TAPC error: unknown values");

SCR1_SVA_TAPC_XCHECK_NEGCLK : assert property (
    @(negedge tapc_tck) disable iff (tap_fsm_ff != SCR1_TAP_STATE_DR_SHIFT)
    !$isunknown({tapcsync2tapc_ch_tdo_i})
) else $error("TAPC @negedge error: unknown values");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_tapc

`endif // SCR1_DBG_EN

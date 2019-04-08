/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file <scr1_scu.sv>
/// @brief System Control Unit (SCU)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN

module scr1_scu #(
    parameter bit SCR1_SCU_CFG_RESET_INPUTS_SYNC    = 1 // Reset inputs are: 1 - synchronous, 0 -asynchronous
) (
    // Global signals
    input  logic                                      pwrup_rst_n,      // Power-Up Reset
    input  logic                                      rst_n,            // Regular Reset
    input  logic                                      cpu_rst_n,        // CPU Reset
    input  logic                                      test_mode,        // DFT Test Mode
    input  logic                                      test_rst_n,       // DFT Test Reset
    input  logic                                      clk,              // SCU clock
    // TAPC scan-chains
    input  logic                                      tapc_ch_sel,      // TAPC Chain Select
    input  logic                                      tapc_ch_id,       // TAPC Chain ID
    input  logic                                      tapc_ch_capture,  // TAPC Chain Capture
    input  logic                                      tapc_ch_shift,    // TAPC Chain Shift
    input  logic                                      tapc_ch_update,   // TAPC Chain Update
    input  logic                                      tapc_ch_tdi,      // TAPC Chain TDI
    output logic                                      tapc_ch_tdo,      // TAPC Chain TDO
    // Input sync resets:
    input  logic                                      ndm_rst_n,        // Non-DM Reset input from DM
    input  logic                                      hart_rst_n,       // HART Reset from DM
    // Generated resets and their attributes (qualifiers etc):
    output logic                                      core_rst_n,       // Core Reset
    output logic                                      core_rst_n_qlfy,  // Core Reset Qualifier
    output logic                                      dm_rst_n,         // Debug Module Reset
    output logic                                      hdu_rst_n,        // HART Debug Unit Reset
    output logic                                      hdu_rst_n_qlfy    // HDU Reset Qualifier
);

//======================================================================================================================
// Local Parameters
//======================================================================================================================
localparam int unsigned SCR1_SCU_DR_SYSCTRL_OP_WIDTH    = 2;
localparam int unsigned SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH  = 2;
localparam int unsigned SCR1_SCU_DR_SYSCTRL_DATA_WIDTH  = 4;

//======================================================================================================================
// Local Types
//======================================================================================================================
typedef enum logic [SCR1_SCU_DR_SYSCTRL_OP_WIDTH-1:0] {
    SCR1_SCU_SYSCTRL_OP_WRITE       = 2'h0,
    SCR1_SCU_SYSCTRL_OP_READ        = 2'h1,
    SCR1_SCU_SYSCTRL_OP_SETBITS     = 2'h2,
    SCR1_SCU_SYSCTRL_OP_CLRBITS     = 2'h3,
    SCR1_SCU_SYSCTRL_OP_XXX         = 'X
} type_scr1_scu_sysctrl_op_e;

typedef enum logic [SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH-1:0] {
    SCR1_SCU_SYSCTRL_ADDR_CONTROL   = 2'h0,
    SCR1_SCU_SYSCTRL_ADDR_MODE      = 2'h1,
    SCR1_SCU_SYSCTRL_ADDR_STATUS    = 2'h2,
    SCR1_SCU_SYSCTRL_ADDR_STICKY    = 2'h3,
    SCR1_SCU_SYSCTRL_ADDR_XXX       = 'X
} type_scr1_scu_sysctrl_addr_e;

typedef struct packed {
    logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]  data;
    logic [SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH-1:0]  addr;
    logic [SCR1_SCU_DR_SYSCTRL_OP_WIDTH-1:0]    op;
} type_scr1_scu_sysctrl_dr_s;

typedef struct packed {
    logic [2:0]                                     rsrv;
    logic                                           sys_reset;
} type_scr1_scu_sysctrl_control_reg_s;

typedef struct packed {
    logic [1:0]                                     rsrv;
    logic                                           hdu_rst_mux;
    logic                                           dm_rst_mux;
} type_scr1_scu_sysctrl_mode_reg_s;

typedef struct packed {
    logic                                           hdu_reset;
    logic                                           dm_reset;
    logic                                           core_reset;
    logic                                           sys_reset;
} type_scr1_scu_sysctrl_status_reg_s;

//======================================================================================================================
// Local Signals
//======================================================================================================================

type_scr1_scu_sysctrl_dr_s                          shift_reg;
type_scr1_scu_sysctrl_dr_s                          shadow_reg;
logic                                               dr_capture;
logic                                               dr_shift;
logic                                               dr_update;
logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]          cmd_data;
logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]          reg_data;
//
type_scr1_scu_sysctrl_control_reg_s                 control_reg;
logic                                               control_reg_wr;
type_scr1_scu_sysctrl_mode_reg_s                    mode_reg;
type_scr1_scu_sysctrl_mode_reg_s                    mode_reg_r;
logic                                               mode_reg_wr;
logic                                               mode_reg_wr_r;
type_scr1_scu_sysctrl_status_reg_s                  status_reg_data;
type_scr1_scu_sysctrl_status_reg_s                  status_reg_data_dly;
type_scr1_scu_sysctrl_status_reg_s                  status_reg_data_posedge;
type_scr1_scu_sysctrl_status_reg_s                  sticky_sts_reg;
logic                                               sticky_sts_reg_wr;
//
logic                                               pwrup_rst_n_sync;
logic                                               rst_n_sync;
logic                                               cpu_rst_n_sync;
//
logic                                               sys_rst_n;
logic                                               sys_rst_n_sync;
logic                                               sys_rst_n_qlfy;
logic                                               sys_rst_n_status;
//
logic                                               dm_rst_n_sync;
logic                                               dm_rst_n_qlfy;
logic                                               dm_rst_n_status;
//
logic                                               core_rst_n_sync;
logic                                               core_rst_n_qlfy_sync;
logic                                               core_rst_n_status;
//
logic                                               hdu_rst_n_sync;
logic                                               hdu_rst_n_status;


//======================================================================================================================
// Logic
//======================================================================================================================

// -----------------------------------------------------------------------------
// Scan-chain i/f
// -----------------------------------------------------------------------------
assign dr_capture = tapc_ch_sel & (tapc_ch_id == '0) & tapc_ch_capture;
assign dr_shift   = tapc_ch_sel & (tapc_ch_id == '0) & tapc_ch_shift;
assign dr_update  = tapc_ch_sel & (tapc_ch_id == '0) & tapc_ch_update;

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        shift_reg   <= '0;
    end
    else begin
        if (dr_capture)
            shift_reg <= shadow_reg;
        else if(dr_shift)
            shift_reg <= {tapc_ch_tdi, shift_reg[$bits(type_scr1_scu_sysctrl_dr_s)-1:1]};
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        shadow_reg   <= '0;
    end
    else begin
        if (dr_update) begin
            shadow_reg.op   <= shift_reg.op;
            shadow_reg.addr <= shift_reg.addr;
            shadow_reg.data <= cmd_data;
        end
    end
end

always_comb
begin
    cmd_data = '0;

    if (dr_update) begin
        case (shift_reg.op)
            SCR1_SCU_SYSCTRL_OP_WRITE : begin
                cmd_data = shift_reg.data;
            end
            SCR1_SCU_SYSCTRL_OP_READ : begin
                cmd_data = reg_data;
            end
            SCR1_SCU_SYSCTRL_OP_SETBITS : begin
                cmd_data = reg_data |   shift_reg.data;
            end
            SCR1_SCU_SYSCTRL_OP_CLRBITS : begin
                cmd_data = reg_data & (~shift_reg.data);
            end
            default: begin
            end
        endcase
    end
end

assign tapc_ch_tdo = shift_reg[0];

// -----------------------------------------------------------------------------
// Registers
// -----------------------------------------------------------------------------
always_comb
begin
    control_reg_wr      = 1'b0;
    mode_reg_wr         = 1'b0;
    sticky_sts_reg_wr   = 1'b0;

    if (dr_update && (shift_reg.op != SCR1_SCU_SYSCTRL_OP_READ)) begin
        case (shift_reg.addr)
            SCR1_SCU_SYSCTRL_ADDR_CONTROL : begin
                control_reg_wr      = 1'b1;
            end
            SCR1_SCU_SYSCTRL_ADDR_MODE : begin
                mode_reg_wr         = 1'b1;
            end
            SCR1_SCU_SYSCTRL_ADDR_STICKY : begin
                sticky_sts_reg_wr   = (shift_reg.op == SCR1_SCU_SYSCTRL_OP_CLRBITS) ? 1'b1 : 1'b0;
            end
            default: begin
            end
        endcase
    end
end

always_comb
begin
    reg_data = '0;

    if (dr_update) begin
        case (shift_reg.addr)
            SCR1_SCU_SYSCTRL_ADDR_CONTROL : begin
                reg_data = control_reg;
            end
            SCR1_SCU_SYSCTRL_ADDR_MODE : begin
                reg_data = mode_reg;
            end
            SCR1_SCU_SYSCTRL_ADDR_STATUS : begin
                reg_data = status_reg_data;
            end
            SCR1_SCU_SYSCTRL_ADDR_STICKY : begin
                reg_data = sticky_sts_reg;
            end
            default: begin
                reg_data = 'x;
            end
        endcase
    end
end

// Control Register
always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        control_reg <= '0;
    end
    else begin
        if (control_reg_wr) begin
            control_reg <= cmd_data;
        end
    end
end

// Mode Register
always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        mode_reg      <= '0;
        mode_reg_r    <= '0;
        mode_reg_wr_r <= '0;
    end
    else begin
        if (mode_reg_wr) begin
            mode_reg <= cmd_data;
        end
        mode_reg_wr_r <= mode_reg_wr;
        if (mode_reg_wr_r) begin
            mode_reg_r <= mode_reg;
        end
    end
end

// Status Register
assign status_reg_data.sys_reset    = ~sys_rst_n_status ;
assign status_reg_data.core_reset   = ~core_rst_n_status;
assign status_reg_data.dm_reset     = ~dm_rst_n_status  ;
assign status_reg_data.hdu_reset    = ~hdu_rst_n_status ;

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        status_reg_data_dly <= '0;
    end
    else begin
        status_reg_data_dly <= status_reg_data;
    end
end

assign status_reg_data_posedge = status_reg_data & (~status_reg_data_dly);

// Sticky Status Register
always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        sticky_sts_reg <= '0;
    end
    else begin
        for (int unsigned i = 0; i < $bits(type_scr1_scu_sysctrl_status_reg_s); ++i) begin
            if (status_reg_data_posedge[i]) begin
                sticky_sts_reg[i] <= 1'b1;
            end
            else if (sticky_sts_reg_wr) begin
                sticky_sts_reg[i] <= cmd_data[i];
            end
        end
    end
end

// -----------------------------------------------------------------------------
// Reset logic
// -----------------------------------------------------------------------------
generate

if (SCR1_SCU_CFG_RESET_INPUTS_SYNC)
// reset inputs are synchronous

begin : gen_rst_inputs_sync
    assign pwrup_rst_n_sync     = pwrup_rst_n;
    assign rst_n_sync           = rst_n;
    assign cpu_rst_n_sync       = cpu_rst_n;
end : gen_rst_inputs_sync

else // SCR1_SCU_CFG_RESET_INPUTS_SYNC == 0, - reset inputs are asynchronous

begin : gen_rst_inputs_async
// Power-Up Reset synchronizer
scr1_reset_sync_cell i_pwrup_rstn_reset_sync (
    .rst_n          (pwrup_rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (pwrup_rst_n_sync)
);

// Regular Reset synchronizer
scr1_reset_sync_cell i_rstn_reset_sync (
    .rst_n          (rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (rst_n_sync)
);

// CPU Reset synchronizer
scr1_reset_sync_cell i_cpu_rstn_reset_sync (
    .rst_n          (cpu_rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (cpu_rst_n_sync)
);
end : gen_rst_inputs_async

// end of SCR1_SCU_CFG_RESET_INPUTS_SYNC

endgenerate

// System Reset: sys_rst_n
scr1_reset_buf_qlfy_cell i_sys_rstn_buf_qlfy_cell (
    .rst_n              (pwrup_rst_n_sync),
    .clk                (clk),
    .test_rst_n         (test_rst_n),
    .test_mode          (test_mode),
    .reset_n_in         (sys_rst_n_sync),
    .reset_n_out_qlfy   (sys_rst_n_qlfy),
    .reset_n_out        (sys_rst_n),
    .reset_n_status     (sys_rst_n_status)
);
assign sys_rst_n_sync = (~control_reg.sys_reset) & rst_n_sync;

// Debug Module Reset: dm_rst_n
scr1_reset_buf_cell i_dm_rstn_buf_cell (
    .rst_n              (dm_rst_n_sync),
    .clk                (clk),
    .test_mode          (test_mode),
    .test_rst_n         (test_rst_n),
    .reset_n_in         (1'b1),
    .reset_n_out        (dm_rst_n),
    .reset_n_status     (dm_rst_n_status)
);
assign dm_rst_n_sync = mode_reg_r.dm_rst_mux ? sys_rst_n      : pwrup_rst_n_sync;
assign dm_rst_n_qlfy = mode_reg.dm_rst_mux   ? sys_rst_n_qlfy : 1'b1 ;

// Core Reset: core_rst_n
scr1_reset_buf_qlfy_cell i_core_rstn_buf_qlfy_cell (
    .rst_n              (sys_rst_n),
    .clk                (clk),
    .test_rst_n         (test_rst_n),
    .test_mode          (test_mode),
    .reset_n_in         (core_rst_n_sync),
    .reset_n_out_qlfy   (core_rst_n_qlfy_sync),
    .reset_n_out        (core_rst_n),
    .reset_n_status     (core_rst_n_status)
);
assign core_rst_n_sync      = ndm_rst_n & hart_rst_n & cpu_rst_n_sync;
// Reset qualifier - become active before reset is asserted
assign core_rst_n_qlfy = sys_rst_n_qlfy & core_rst_n_qlfy_sync;


// Hart Debug Unit Reset: hdu_rst_n
scr1_reset_buf_cell i_hdu_rstn_buf_cell (
    .rst_n              (hdu_rst_n_sync),
    .clk                (clk),
    .test_mode          (test_mode),
    .test_rst_n         (test_rst_n),
    .reset_n_in         (1'b1),
    .reset_n_out        (hdu_rst_n),
    .reset_n_status     (hdu_rst_n_status)
);
assign hdu_rst_n_sync = mode_reg_r.hdu_rst_mux ? pwrup_rst_n_sync : core_rst_n;
assign hdu_rst_n_qlfy = mode_reg.hdu_rst_mux   ? 1'b1             : core_rst_n_qlfy;

endmodule : scr1_scu

`endif // SCR1_DBGC_EN


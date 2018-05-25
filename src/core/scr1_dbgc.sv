/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_dbgc.sv>
/// @brief      Debug Controller (DBGC)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_csr.svh"
`include "scr1_dbgc.svh"

module scr1_dbgc (
    // Common signals
    input  logic                                        rst_n,              // DBGC Reset
    input  logic                                        clk,                // DBGC Clock
`ifdef SCR1_CLKCTRL_EN
    output logic                                        sleep_rdy,          // Sleep Ready: 1 if DBGC is ready for clock gating
    output logic                                        sleep_wakeup,       // Sleep Wakeup: 1 - request for wake-up
`endif // SCR1_CLKCTRL_EN
    // FUSE I/F
    input  logic [`SCR1_XLEN-1:0]                       fuse_mhartid,       // Fuse MHARTID input
    // DAP scan-chains
    input  logic                                        dap_ch_sel,         // DAP Chain Select
    input  logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]        dap_ch_id,          // DAP Chain Identificator
    input  logic                                        dap_ch_capture,     // DAP Chain Capture
    input  logic                                        dap_ch_shift,       // DAP Chain Shift
    input  logic                                        dap_ch_update,      // DAP Chain Update
    input  logic                                        dap_ch_tdi,         // DAP Chain TDI
    output logic                                        dap_ch_tdo,         // DAP Chain TDO
    // Core Debug I/F
    output logic                                        core_rst_ctrl,      // Core Reset Control output
    input  logic                                        core_rst_sts,       // Core Reset Status input
    input  type_scr1_dbgc_core_busy_s                   core_state_busy,    // Core Busy State
    // -- Hart[0] part:
    output logic                                        hart_rst_ctrl,      // Hart Reset Control output
    input  logic                                        hart_rst_sts,       // Hart Reset Status input
    output type_scr1_dbgc_hart_dbg_mode_e               hart_dbg_cmd,       // Hart Debug Command: 1 - Debug Halt;
                                                                            //      0 - go to SCR1_RUN state (w/ RunControl Options below)
    output logic                                        hart_dbg_cmd_req,   // Hart Debug Command Request
    input  logic                                        hart_dbg_cmd_ack,   // Hart Debug Command Acknowledge:
                                                                            //      1 - ACK on debug request (debug command execution started Ok)
    input  logic                                        hart_dbg_cmd_nack,  // Hart Debug Command Negative Acknowledge:
                                                                            //      1 - NACK on debug request (debug command refused, there are problems)
    output type_scr1_dbgc_hart_runctrl_s                hart_dbg_runctrl,   // Hart Debug RunControl Options structure
    input  type_scr1_dbgc_hart_state_s                  hart_dbg_state,     // Hart Debug State structure
    output logic [SCR1_DBGC_DBG_CORE_INSTR_WIDTH-1:0]   hart_dbg_instr,     // Instruction from DBGC to core
    output logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]     hart_dbg_dreg_out,  // Debug Data Register (DDR) output
    input  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]     hart_dbg_dreg_in,   // Debug Data Register (DDR) input
    input  logic                                        hart_dbg_dreg_wr,   // 1 - write to DDR (from core)
    input  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]     hart_dbg_pcsample   // PC Sample register input
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Debug Access Port (DAP)
logic                                       dap_head_shift_reg_sel;
logic                                       dap_head_shift_reg_tdo;
logic                                       dap_head_shift_reg_mux;
logic [SCR1_DBGC_DAP_HEADER_REG_WIDTH-1:0]  dap_head_shift_reg_pdin;
logic [SCR1_DBGC_DAP_HEADER_REG_WIDTH-1:0]  dap_head_shift_reg_pdout;
logic                                       dap_data_shift_reg_sel;
logic                                       dap_data_shift_reg_tdo;
logic                                       dap_data_shift_reg_mux;
logic [SCR1_DBGC_DAP_DATA_REG_WIDTH-1:0]    dap_data_shift_reg_pdin;
logic [SCR1_DBGC_DAP_DATA_REG_WIDTH-1:0]    dap_data_shift_reg_pdout;
type_scr1_dap_ctrl_reg_s                    dap_ctrl_reg;
logic                                       dap_ctrl_reg_wr;
type_scr1_dap_ctrl_reg_s                    dap_lock_state_ctrl_reg;
logic                                       dap_lock_clr;
type_scr1_dbgc_dap_opstatus_s               dap_opstatus;
logic                                       dap_cmd_req;
logic                                       dap_err_fsm_busy;
logic                                       dap_err_fsm_busy_reg;

// DAP Command Decoder
logic [SCR1_DBGC_DAP_OPCODE_REG_WIDTH-1:0]  decod_dap_cmd_opcode_reg;
logic [SCR1_DBGC_DAP_OPCODE_REG_WIDTH-1:0]  decod_dap_cmd_opcode_mux;
type_scr1_dbgc_dap_cmd_opcode_regtrans_s    decod_dap_cmd_opcode_regtrans;
const type_scr1_dbgc_dap_cmd_opcode_regtrans_s   decod_dap_cmd_opcode_regtrans_rd_core_dbgid = '{1'b0, SCR1_DBGC_CORE_REGS_DEBUG_ID};
type_scr1_dbgc_fsm_opcode_e                 decod_fsm_opcode;
type_scr1_dbgc_fsm_opcode_e                 decod_fsm_opcode_reg;
logic                                       decod_err_invld_unit_id;
logic                                       decod_err_invld_fgrp_id;
logic                                       decod_err_invld_dap_hart;
logic                                       decod_err_invld_dap_opcode_fsm_hart;
logic                                       decod_err_invld_dap_opcode_fsm_core;
logic                                       decod_err_invld_dap_opcode_hart;
logic                                       decod_err_invld_dap_opcode_hart_reg;
logic                                       decod_err_invld_dap_opcode_core;
logic                                       decod_err_invld_dap_opcode_core_reg;
type_scr1_dbgc_hart_reg_sel_s               decod_hart_reg_wr;
type_scr1_dbgc_core_reg_sel_s               decod_core_reg_wr;
logic                                       decod_hart_dbg_cmd_req;
type_scr1_dbgc_hart_dbg_mode_e              decod_hart_dbg_cmd;
type_scr1_dbgc_hart_runctrl_s               decod_hart_runctrl;
logic                                       decod_dap_cmd_req;
logic                                       decod_dap_update_dst_sel; // 0 - DDR, 1 - DCIR
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    decod_ddr_mux;
type_scr1_dbgc_lock_context_s               decod_lock_context;
logic                                       decod_hart_sticky_clr;
type_scr1_dbgc_dap_cmd_opcode_dbgctrl_ext_s decod_hart_dbgcmd_dbgctrl;
logic                                       decod_hart_pc_sample_reg_wr;

// FSM
type_scr1_dbgc_fsm_state_e                  fsm_state_reg;
type_scr1_dbgc_fsm_state_e                  fsm_state_next;
logic                                       fsm_state_ready;
logic                                       fsm_opcode_reg_wr;
type_scr1_dbgc_fsm_ddr_input_sel_e          fsm_ddr_input_sel;
logic                                       fsm_ddr_wr;
logic                                       fsm_dcir_wr;
logic                                       fsm_regblock_wr;
logic                                       fsm_sampling_wr;
logic                                       fsm_except_lock_set;
logic                                       fsm_hart_cmd_req;
logic                                       fsm_hart_cmd_reg_wr;
logic                                       fsm_hart_cmd_dmode_entr;
logic                                       fsm_hart_cmd_dmode_exit;
logic                                       fsm_hart_cmd_err_nack;
logic                                       fsm_hart_cmd_err_timeout;
logic                                       fsm_hart_cmd_err_illeg_dbg_context;
logic                                       fsm_hart_cmd_err_unexp_reset;

// State Registers
logic                                       state_lock_set;
logic                                       state_lock_reg;
type_scr1_dbgc_hart_dbg_mode_e              state_dmode_reg;
logic                                       state_dmode_set;
logic                                       state_dmode_clr;
logic                                       state_core_err;
logic                                       state_core_err_delay;
logic                                       state_core_err_posedge;
logic                                       state_hart_err;
logic                                       state_hart_err_delay;
logic                                       state_hart_err_posedge;
logic                                       state_hart_err_hwthread;
logic                                       state_hart_except;
type_scr1_dbgc_dbghalt_s                    state_hart_dmode_cause;
logic                                       state_hart_rst_exit_brk_req;
logic                                       state_core_rst_delay;
logic                                       state_core_rst_posedge;
logic                                       state_hart_rst_delay;
logic                                       state_hart_rst_posedge;
logic                                       state_hart_dmode_cause_rst_entr;
logic                                       state_hart_dmode_cause_rst_entr_reg;

// Debug CSRs

// Debug Core Registers
type_scr1_dbgc_core_dbg_ctrl_reg_s          core_dcr_in;
type_scr1_dbgc_core_dbg_ctrl_reg_s          core_dcr_out;
logic                                       core_dcr_core_rst_reg;
type_scr1_dbgc_hart_irq_dsbl_e              core_dcr_irq_dsbl_reg;
logic                                       core_dcr_hart0_rst_reg;
type_scr1_dbgc_core_dbg_sts_reg_s           core_dsr_in;
type_scr1_dbgc_core_dbg_sts_reg_s           core_dsr_out;
logic                                       core_dsr_rst_stky_reg;
logic                                       core_dsr_err_stky_reg;
logic                                       core_dsr_hart0_err_stky_reg;
type_scr1_dbgc_core_dbg_pipe_sts_reg_s      core_dpsr_out;

// Debug HART_0 Registers
type_scr1_dbgc_hart_dbg_ctrl_reg_s          hart_dcr_in;
type_scr1_dbgc_hart_dbg_ctrl_reg_s          hart_dcr_out;
logic                                       hart_dcr_rst_reg;
logic                                       hart_dcr_pc_admt_dsbl_reg;
type_scr1_dbgc_hart_dbg_sts_reg_s           hart_dsr_out;
logic                                       hart_dsr_rst_stky_reg;
logic                                       hart_dsr_lock_stky_reg;
type_scr1_dbgc_hart_dmode_enbl_reg_s        hart_dmer_in;
type_scr1_dbgc_hart_dmode_enbl_reg_s        hart_dmer_out;
type_scr1_dbgc_dmode_en_s                   hart_dmer_reg;
type_scr1_dbgc_hart_dmode_cause_reg_s       hart_dmcr_out;
type_scr1_dbgc_dbghalt_s                    hart_dmcr_reg;
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    hart_ddr_reg;
logic [SCR1_DBGC_DBG_CORE_INSTR_WIDTH-1:0]  hart_dcir_reg;
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    hart_pcsample_reg;

// Core I/F
logic                                       core_if_rst_ctrl;
// -- Hart[0] part:
logic                                       hart_if_rst_ctrl;
type_scr1_dbgc_hart_dbg_mode_e              hart_if_dbg_cmd_reg;
type_scr1_dbgc_hart_runctrl_s               hart_if_runctrl_reg;
logic                                       hart_if_cmd_err_nack_reg;
logic                                       hart_if_cmd_err_timeout_reg;
logic                                       hart_if_cmd_err_illeg_dbg_context_reg;
logic                                       hart_if_cmd_err_unexp_reset_reg;

//-------------------------------------------------------------------------------
// Debug Access Port (DAP)
//-------------------------------------------------------------------------------
always_comb begin
    dap_head_shift_reg_sel      = 1'b0;
    dap_data_shift_reg_sel      = 1'b0;
    dap_ctrl_reg_wr             = 1'b0;
    dap_cmd_req                 = 1'b0;
    dap_err_fsm_busy            = 1'b0;
    dap_lock_clr                = 1'b0;

    if (dap_ch_sel) begin
        case (dap_ch_id)

            SCR1_DAP_CHAIN_ID_DBG_ID : begin
                dap_data_shift_reg_sel      = 1'b1;
            end

            SCR1_DAP_CHAIN_ID_DBG_STATUS : begin
                dap_data_shift_reg_sel      = 1'b1;
            end

            SCR1_DAP_CHAIN_ID_DAP_CTRL : begin
                dap_head_shift_reg_sel      = 1'b1;
                if (fsm_state_ready) begin
                    if (~state_lock_reg) begin
                        dap_ctrl_reg_wr     = dap_ch_update;
                    end
                    else begin
                        if (dap_head_shift_reg_pdout == {SCR1_DBGC_UNIT_ID_HART_0, SCR1_DBGC_FGRP_HART_DBGCMD}) begin
                            dap_ctrl_reg_wr = dap_ch_update;
                        end
                    end
                end
                else begin
                    dap_err_fsm_busy        = dap_ch_update;
                end
            end

            SCR1_DAP_CHAIN_ID_DAP_CTRL_RD : begin
                dap_head_shift_reg_sel      = 1'b1;
            end

            SCR1_DAP_CHAIN_ID_DAP_CMD : begin
                dap_head_shift_reg_sel      = 1'b1;
                dap_data_shift_reg_sel      = 1'b1;
                if (~state_lock_reg) begin
                    if (fsm_state_ready) begin
                        dap_cmd_req         = dap_ch_update;
                    end
                    else begin
                        dap_err_fsm_busy    = dap_ch_update;
                    end
                end
                else begin
                    if (  (dap_ctrl_reg == {SCR1_DBGC_UNIT_ID_HART_0, SCR1_DBGC_FGRP_HART_DBGCMD})
                        & (dap_head_shift_reg_pdout == SCR1_DBGC_DAP_OPCODE_DBGCMD_UNLOCK)
                    ) begin
                        dap_lock_clr        = dap_ch_update;
                    end
                end
            end

            SCR1_DAP_CHAIN_ID_DBG_PIPE_STS : begin
                dap_data_shift_reg_sel      = 1'b1;
            end

            SCR1_DAP_CHAIN_ID_TARGET_ID : begin
                dap_data_shift_reg_sel      = 1'b1;
            end

            default : begin
                dap_head_shift_reg_sel      = 1'b0;
                dap_data_shift_reg_sel      = 1'b0;
                dap_ctrl_reg_wr             = 1'b0;
                dap_cmd_req                 = 1'b0;
                dap_err_fsm_busy            = 1'b0;
                dap_lock_clr                = 1'b0;
            end
        endcase
    end
end

always_comb begin
    dap_head_shift_reg_pdin = '0;
    dap_data_shift_reg_pdin = '0;

    case (dap_ch_id)

        SCR1_DAP_CHAIN_ID_DBG_ID : begin
            dap_data_shift_reg_pdin = SCR1_DBGC_DAP_DBG_ID_VALUE;
        end

        SCR1_DAP_CHAIN_ID_DBG_STATUS : begin
            dap_data_shift_reg_pdin = core_dsr_out;
        end

        SCR1_DAP_CHAIN_ID_DAP_CTRL : begin
            dap_head_shift_reg_pdin = dap_opstatus;
        end

        SCR1_DAP_CHAIN_ID_DAP_CTRL_RD : begin
            dap_head_shift_reg_pdin = dap_ctrl_reg;
        end

        SCR1_DAP_CHAIN_ID_DAP_CMD : begin
            dap_head_shift_reg_pdin = dap_opstatus;
            dap_data_shift_reg_pdin = hart_ddr_reg;
        end

        SCR1_DAP_CHAIN_ID_DBG_PIPE_STS : begin
            dap_data_shift_reg_pdin = core_dpsr_out;
        end

        SCR1_DAP_CHAIN_ID_TARGET_ID : begin
            dap_data_shift_reg_pdin = SCR1_DBGC_DAP_TARGET_ID_VALUE;
        end

        default : begin
            dap_head_shift_reg_pdin = '0;
            dap_data_shift_reg_pdin = '0;
        end
    endcase
end

always_comb begin
    dap_opstatus        = '0;
    dap_opstatus.ready  = fsm_state_ready;
    dap_opstatus.lock   = state_lock_reg;
    dap_opstatus.error  = state_core_err;
    dap_opstatus.except = state_hart_except;
end

scr1_tapc_shift_reg #(
        .SCR1_WIDTH      (SCR1_DBGC_DAP_HEADER_REG_WIDTH),
        .SCR1_RESET_VALUE(SCR1_DBGC_DAP_HEADER_REG_WIDTH'(0))
    )
    i_dap_head_shift_reg (
        .clk            (clk),
        .rst_n          (rst_n),
        .rst_n_sync     (1'b1),
        .fsm_dr_select  (dap_head_shift_reg_sel),
        .fsm_dr_capture (dap_ch_capture),
        .fsm_dr_shift   (dap_ch_shift),
        .din_serial     (dap_ch_tdi),
        .din_parallel   (dap_head_shift_reg_pdin),
        .dout_serial    (dap_head_shift_reg_tdo),
        .dout_parallel  (dap_head_shift_reg_pdout)
);
assign dap_head_shift_reg_mux   = dap_head_shift_reg_sel
                                ? dap_head_shift_reg_tdo
                                : dap_ch_tdi;

scr1_tapc_shift_reg #(
        .SCR1_WIDTH      (SCR1_DBGC_DAP_DATA_REG_WIDTH),
        .SCR1_RESET_VALUE(SCR1_DBGC_DAP_DATA_REG_WIDTH'(0))
    )
    i_dap_data_shift_reg (
        .clk            (clk),
        .rst_n          (rst_n),
        .rst_n_sync     (1'b1),
        .fsm_dr_select  (dap_data_shift_reg_sel),
        .fsm_dr_capture (dap_ch_capture),
        .fsm_dr_shift   (dap_ch_shift),
        .din_serial     (dap_head_shift_reg_mux),
        .din_parallel   (dap_data_shift_reg_pdin),
        .dout_serial    (dap_data_shift_reg_tdo),
        .dout_parallel  (dap_data_shift_reg_pdout)
);
assign dap_ch_tdo               = dap_data_shift_reg_mux;
assign dap_data_shift_reg_mux   = dap_data_shift_reg_sel
                                ? dap_data_shift_reg_tdo
                                : dap_head_shift_reg_mux;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dap_ctrl_reg.unit   <= SCR1_DBGC_UNIT_ID_HART_0;
        dap_ctrl_reg.fgrp   <= SCR1_DBGC_FGRP_CORE_REGTRANS;
    end
    else begin
        if (dap_ctrl_reg_wr) begin
            dap_ctrl_reg    <= dap_head_shift_reg_pdout;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dap_lock_state_ctrl_reg.unit    <= SCR1_DBGC_UNIT_ID_HART_0;
        dap_lock_state_ctrl_reg.fgrp    <= SCR1_DBGC_FGRP_CORE_REGTRANS;
    end
    else begin
        if (state_lock_set) begin
            dap_lock_state_ctrl_reg     <= dap_ctrl_reg;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dap_err_fsm_busy_reg        <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            dap_err_fsm_busy_reg    <= 1'b0;
        end
        else if (dap_err_fsm_busy) begin
            dap_err_fsm_busy_reg    <= 1'b1;
        end
    end
end

//-------------------------------------------------------------------------------
// DAP Command Decoder
//-------------------------------------------------------------------------------
always_comb begin
    decod_err_invld_dap_opcode_fsm_hart = 1'b0;
    decod_err_invld_dap_opcode_fsm_core = 1'b0;
    decod_dap_cmd_req                   = 1'b0;
    decod_dap_cmd_opcode_mux            = dap_head_shift_reg_pdout;
    decod_hart_pc_sample_reg_wr         = 1'b0;
    decod_dap_update_dst_sel            = 1'b0; // Default destination for DR-Update: DDR
    decod_fsm_opcode                    = SCR1_DBGC_FSM_OPCODE_REGTRANS;

    case (dap_ctrl_reg.unit)

        SCR1_DBGC_UNIT_ID_HART_0 : begin
            case (dap_ctrl_reg.fgrp)

                SCR1_DBGC_FGRP_HART_REGTRANS : begin
                    decod_dap_cmd_req                   = dap_cmd_req;
                    decod_fsm_opcode                    = SCR1_DBGC_FSM_OPCODE_REGTRANS;
                    // If command is read of PC_Sample -> enable PC latching
                    if (dap_head_shift_reg_pdout == {1'b0, SCR1_DBGC_HART_REGS_PC_SAMPLE}) begin
                        decod_hart_pc_sample_reg_wr     = fsm_sampling_wr;
                    end
                end

                SCR1_DBGC_FGRP_HART_DBGCMD : begin
                    case (dap_head_shift_reg_pdout)

                        SCR1_DBGC_DAP_OPCODE_DBGCMD_DBG_CTRL : begin
                            decod_dap_cmd_req           = dap_cmd_req;
                            decod_fsm_opcode            = SCR1_DBGC_FSM_OPCODE_DBGCTRL;
                        end

                        SCR1_DBGC_DAP_OPCODE_DBGCMD_CORE_EXEC : begin
                            decod_dap_cmd_req           = dap_cmd_req;
                            decod_dap_update_dst_sel    = 1'b1; // Destination for DR-Update: DCIR
                            decod_fsm_opcode            = SCR1_DBGC_FSM_OPCODE_CORE_EXEC;
                        end

                        SCR1_DBGC_DAP_OPCODE_DBGCMD_DBGDATA_WR : begin
                            decod_dap_cmd_req           = dap_cmd_req;
                            // OpCode modification (change to REGTRANS layout): write = 1, reg_index = DBG_DATA
                            decod_dap_cmd_opcode_mux    = {1'b1, SCR1_DBGC_HART_REGS_DBG_DATA};
                            decod_fsm_opcode            = SCR1_DBGC_FSM_OPCODE_REGTRANS;
                        end

                        SCR1_DBGC_DAP_OPCODE_DBGCMD_UNLOCK : begin
                            decod_dap_cmd_req           = dap_cmd_req;
                            decod_fsm_opcode            = SCR1_DBGC_FSM_OPCODE_UNLOCK;
                        end

                        default : begin
                            decod_err_invld_dap_opcode_fsm_hart = dap_cmd_req;
                        end
                    endcase
                end

                SCR1_DBGC_FGRP_HART_CSR_CAP : begin
                    decod_dap_cmd_req                   = dap_cmd_req;
                    decod_fsm_opcode                    = SCR1_DBGC_FSM_OPCODE_REGTRANS;
                end

                default : begin
                    decod_err_invld_dap_opcode_fsm_hart = dap_cmd_req;
                end
            endcase
        end

        SCR1_DBGC_UNIT_ID_CORE : begin
            case (dap_ctrl_reg.fgrp)

                SCR1_DBGC_FGRP_CORE_REGTRANS : begin
                    decod_dap_cmd_req                   = dap_cmd_req;
                    decod_fsm_opcode                    = SCR1_DBGC_FSM_OPCODE_REGTRANS;
                end

                default : begin
                    decod_err_invld_dap_opcode_fsm_core = dap_cmd_req;
                end
            endcase
        end

        default : begin
            decod_err_invld_dap_opcode_fsm_core         = dap_cmd_req;
        end
    endcase
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        decod_fsm_opcode_reg        <= SCR1_DBGC_FSM_OPCODE_REGTRANS;
    end
    else begin
        if (fsm_opcode_reg_wr) begin
            decod_fsm_opcode_reg    <= decod_fsm_opcode;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        decod_dap_cmd_opcode_reg        <= decod_dap_cmd_opcode_regtrans_rd_core_dbgid;
    end
    else begin
        if (fsm_opcode_reg_wr) begin
            decod_dap_cmd_opcode_reg    <= decod_dap_cmd_opcode_mux;
        end
    end
end
assign decod_dap_cmd_opcode_regtrans    = decod_dap_cmd_opcode_reg;

always_comb begin
    decod_core_reg_wr                   = '0;
    decod_hart_reg_wr                   = '0;
    decod_hart_dbg_cmd_req              = 1'b0;
    decod_hart_dbg_cmd                  = hart_if_dbg_cmd_reg;
    decod_hart_runctrl                  = hart_if_runctrl_reg;
    decod_ddr_mux                       = hart_ddr_reg;
    decod_hart_sticky_clr               = 1'b0;
    decod_err_invld_dap_opcode_hart     = 1'b0;
    decod_err_invld_dap_opcode_core     = 1'b0;

    if (fsm_state_reg == SCR1_DBGC_FSM_STATE_IDLE) begin
        decod_hart_runctrl.dmode_en.rst_brk = state_hart_rst_exit_brk_req;
    end
    else begin
        case (decod_fsm_opcode_reg)

            SCR1_DBGC_FSM_OPCODE_REGTRANS : begin
                decod_hart_runctrl.dmode_en.rst_brk = state_hart_rst_exit_brk_req;
                case (dap_ctrl_reg.unit)

                    SCR1_DBGC_UNIT_ID_HART_0 : begin
                        case (dap_ctrl_reg.fgrp)

                            SCR1_DBGC_FGRP_HART_REGTRANS : begin
                                if (decod_dap_cmd_opcode_regtrans.write) begin
                                    case (decod_dap_cmd_opcode_regtrans.index)

                                        SCR1_DBGC_HART_REGS_DBG_CTRL : begin
                                            decod_hart_reg_wr.ctrl          = fsm_regblock_wr;
                                        end

                                        SCR1_DBGC_HART_REGS_DMODE_ENBL : begin
                                            decod_hart_reg_wr.dmode_en      = fsm_regblock_wr;
                                        end

                                        SCR1_DBGC_HART_REGS_CORE_INSTR : begin
                                            decod_hart_reg_wr.dcir          = fsm_regblock_wr;
                                        end

                                        SCR1_DBGC_HART_REGS_DBG_DATA : begin
                                            decod_hart_reg_wr.ddr           = fsm_regblock_wr;
                                        end

                                        default : begin
                                            decod_err_invld_dap_opcode_hart = fsm_regblock_wr;
                                        end
                                    endcase
                                end
                                else begin
                                    decod_hart_reg_wr.ddr = fsm_regblock_wr;
                                    case (decod_dap_cmd_opcode_regtrans.index)

                                        SCR1_DBGC_HART_REGS_DBG_CTRL : begin
                                            decod_ddr_mux   = hart_dcr_out;
                                        end

                                        SCR1_DBGC_HART_REGS_DBG_STS : begin
                                            decod_ddr_mux   = hart_dsr_out;
                                        end

                                        SCR1_DBGC_HART_REGS_DMODE_ENBL : begin
                                            decod_ddr_mux   = hart_dmer_out;
                                        end

                                        SCR1_DBGC_HART_REGS_DMODE_CAUSE : begin
                                            decod_ddr_mux   = hart_dmcr_out;
                                        end

                                        SCR1_DBGC_HART_REGS_CORE_INSTR : begin
                                            decod_ddr_mux   = hart_dcir_reg;
                                        end

                                        SCR1_DBGC_HART_REGS_DBG_DATA : begin
                                            decod_ddr_mux   = hart_ddr_reg;
                                        end

                                        SCR1_DBGC_HART_REGS_PC_SAMPLE : begin
                                            decod_ddr_mux   = hart_pcsample_reg;
                                        end

                                        default : begin
                                            decod_err_invld_dap_opcode_hart = fsm_regblock_wr;
                                        end
                                    endcase
                                end
                            end

                            SCR1_DBGC_FGRP_HART_CSR_CAP : begin
                                if (decod_dap_cmd_opcode_regtrans.write) begin
                                    decod_err_invld_dap_opcode_hart = fsm_regblock_wr;
                                end
                                else begin
                                    decod_hart_reg_wr.ddr   = fsm_regblock_wr;
                                    case (decod_dap_cmd_opcode_regtrans.index)
                                        SCR1_DBGC_HART_CSRS_MVENDORID   : decod_ddr_mux = SCR1_CSR_MVENDORID;
                                        SCR1_DBGC_HART_CSRS_MARCHID     : decod_ddr_mux = SCR1_CSR_MARCHID;
                                        SCR1_DBGC_HART_CSRS_MIMPID      : decod_ddr_mux = SCR1_CSR_MIMPID;
                                        SCR1_DBGC_HART_CSRS_MHARTID     : decod_ddr_mux = fuse_mhartid;
                                        SCR1_DBGC_HART_CSRS_MISA        : decod_ddr_mux = SCR1_CSR_MISA;
                                        default                         : begin
                                            decod_err_invld_dap_opcode_hart = fsm_regblock_wr;
                                        end
                                    endcase
                                end
                            end
                            default : begin
                            end
                        endcase
                    end

                    SCR1_DBGC_UNIT_ID_CORE : begin
                        if (decod_dap_cmd_opcode_regtrans.write) begin
                            case (decod_dap_cmd_opcode_regtrans.index)

                                SCR1_DBGC_CORE_REGS_DBG_CTRL : begin
                                    decod_core_reg_wr.ctrl          = fsm_regblock_wr;
                                end

                                SCR1_DBGC_CORE_REGS_DBG_STS : begin
                                    decod_core_reg_wr.sts           = fsm_regblock_wr;
                                end

                                default : begin
                                    decod_err_invld_dap_opcode_core = fsm_regblock_wr;
                                end
                            endcase
                        end
                        else begin
                            decod_hart_reg_wr.ddr = fsm_regblock_wr;
                            case (decod_dap_cmd_opcode_regtrans.index)

                                SCR1_DBGC_CORE_REGS_DEBUG_ID : begin
                                    decod_ddr_mux   = SCR1_DBGC_DAP_DBG_ID_VALUE;
                                end

                                SCR1_DBGC_CORE_REGS_DBG_CTRL : begin
                                    decod_ddr_mux   = core_dcr_out;
                                end

                                SCR1_DBGC_CORE_REGS_DBG_STS : begin
                                    decod_ddr_mux   = core_dsr_out;
                                end

                                SCR1_DBGC_CORE_REGS_DBG_PIPE_STS : begin
                                    decod_ddr_mux   = core_dpsr_out;
                                end

                                SCR1_DBGC_CORE_REGS_DBG_TGT_ID : begin
                                    decod_ddr_mux   = SCR1_DBGC_DAP_TARGET_ID_VALUE;
                                end

                                default : begin
                                    decod_err_invld_dap_opcode_core = fsm_regblock_wr;
                                end
                            endcase
                        end
                    end

                    default : begin
                        decod_err_invld_dap_opcode_core = fsm_regblock_wr;
                    end
                endcase
            end

            SCR1_DBGC_FSM_OPCODE_DBGCTRL : begin
                // Case identification is simple as code already has been analyzed
                // at FSM opcode determination stage
                case (state_dmode_reg)
                    SCR1_DBGC_HART_RUN_MODE : begin
                        decod_hart_dbg_cmd_req  =  decod_hart_dbgcmd_dbgctrl.dm_halt;
                        decod_hart_dbg_cmd      = (decod_hart_dbgcmd_dbgctrl.dm_halt)
                                                ? SCR1_DBGC_HART_DBG_MODE
                                                : SCR1_DBGC_HART_RUN_MODE;
                    end
                    SCR1_DBGC_HART_DBG_MODE : begin
                        decod_hart_dbg_cmd_req  =  decod_hart_dbgcmd_dbgctrl.dm_resume;
                        decod_hart_dbg_cmd      = (decod_hart_dbgcmd_dbgctrl.dm_resume)
                                                ? SCR1_DBGC_HART_RUN_MODE
                                                : SCR1_DBGC_HART_DBG_MODE;
                    end
                    default : begin
                        decod_hart_dbg_cmd_req  = 1'b0;
                        decod_hart_dbg_cmd      = SCR1_DBGC_HART_RUN_MODE;
                    end
                endcase
                decod_hart_sticky_clr           = (decod_hart_dbgcmd_dbgctrl.sticky_clr)
                                                ? fsm_regblock_wr
                                                : 1'b0;
                if (decod_hart_dbg_cmd_req) begin
                    case (decod_hart_dbg_cmd)
                        SCR1_DBGC_HART_RUN_MODE : begin
                            // Prepare new actual value for RunCtrl
                            decod_hart_runctrl.irq_dsbl         = core_dcr_irq_dsbl_reg;
                            decod_hart_runctrl.fetch_src        = SCR1_DBGC_HART_FETCH_SRC_NORMAL;
                            decod_hart_runctrl.pc_advmt_dsbl    = hart_dcr_pc_admt_dsbl_reg;
                            decod_hart_runctrl.dmode_en         = hart_dmer_reg;
                            decod_hart_runctrl.brkpt_hw_dsbl    = 1'b0;
                        end
                        SCR1_DBGC_HART_DBG_MODE : begin
                            // Just save RunCtrl state had been effective during SCR1_RUN mode
                        end
                        default : begin
                            decod_hart_runctrl = '0;
                        end
                    endcase
                end
                else begin
                    decod_hart_runctrl.dmode_en.rst_brk = state_hart_rst_exit_brk_req;
                end
            end

            SCR1_DBGC_FSM_OPCODE_CORE_EXEC : begin
                // Case identification is simple as code already has been analyzed
                // at FSM opcode determination stage
                if (~hart_rst_sts) begin
                    decod_hart_dbg_cmd                  = SCR1_DBGC_HART_RUN_MODE;
                    decod_hart_runctrl.irq_dsbl         = SCR1_DBGC_HART_IRQ_DSBL_ACTIVE;
                    decod_hart_runctrl.fetch_src        = SCR1_DBGC_HART_FETCH_SRC_DBGC;
                    decod_hart_runctrl.pc_advmt_dsbl    = hart_dcr_pc_admt_dsbl_reg;
                    decod_hart_runctrl.dmode_en.sstep   = 1'b1;
                    decod_hart_runctrl.brkpt_hw_dsbl    = 1'b1;
                end
                else begin
                    decod_hart_runctrl.dmode_en.rst_brk = state_hart_rst_exit_brk_req;
                end
            end

            SCR1_DBGC_FSM_OPCODE_UNLOCK : begin
                // Case identification is simple as code already has been analyzed
                // at FSM opcode determination stage
                // The case works only if UNLOCK is applied to unlocked DBGC,
                // and might be used for near loopback test (Chain (tdi) -> ShiftReg In ->
                // (@ DR-Update state) -> DDR -> (@ next DR-Capture) -> Shift-out -> chain (tdo)).
            end
            default : begin
                decod_core_reg_wr                       = '0;
                decod_hart_reg_wr                       = '0;
                decod_hart_dbg_cmd_req                  = 1'b0;
                decod_hart_dbg_cmd                      = SCR1_DBGC_HART_RUN_MODE;
                decod_hart_runctrl                      = '0;
                decod_ddr_mux                           = '0;
                decod_hart_sticky_clr                   = 1'b0;
                decod_err_invld_dap_opcode_hart         = 1'b0;
                decod_err_invld_dap_opcode_core         = 1'b0;
            end
        endcase
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        decod_err_invld_dap_opcode_hart_reg     <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            decod_err_invld_dap_opcode_hart_reg <= 1'b0;
        end
        else if (
              (decod_err_invld_dap_opcode_fsm_hart)
            | (decod_err_invld_dap_opcode_hart)
        ) begin
            decod_err_invld_dap_opcode_hart_reg <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        decod_err_invld_dap_opcode_core_reg     <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            decod_err_invld_dap_opcode_core_reg <= 1'b0;
        end
        else if (
              (decod_err_invld_dap_opcode_fsm_core)
            | (decod_err_invld_dap_opcode_core)
        ) begin
            decod_err_invld_dap_opcode_core_reg <= 1'b1;
        end
    end
end

assign decod_lock_context.dap_ctrl      = dap_lock_state_ctrl_reg;
assign decod_lock_context.dap_opcode    = decod_dap_cmd_opcode_reg;
assign decod_lock_context.fsm_opcode    = decod_fsm_opcode_reg;
assign decod_lock_context.rsrv          = '0;

assign decod_hart_dbgcmd_dbgctrl        = hart_ddr_reg;

//-------------------------------------------------------------------------------
// Debug Controller's FSM
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm_state_reg <= SCR1_DBGC_FSM_STATE_IDLE;
    end
    else begin
        fsm_state_reg <= fsm_state_next;
    end
end

always_comb begin
    fsm_state_ready                     = 1'b0;
    fsm_opcode_reg_wr                   = 1'b0;
    fsm_ddr_wr                          = 1'b0;
    fsm_dcir_wr                         = 1'b0;
    fsm_regblock_wr                     = 1'b0;
    fsm_sampling_wr                     = 1'b0;
    fsm_except_lock_set                 = 1'b0;
    fsm_hart_cmd_req                    = 1'b0;
    fsm_hart_cmd_reg_wr                 = 1'b0;
    fsm_hart_cmd_dmode_entr             = 1'b0;
    fsm_hart_cmd_dmode_exit             = 1'b0;
    fsm_hart_cmd_err_nack               = 1'b0;
    fsm_hart_cmd_err_timeout            = 1'b0;
    fsm_hart_cmd_err_illeg_dbg_context  = 1'b0;
    fsm_hart_cmd_err_unexp_reset        = 1'b0;
    fsm_ddr_input_sel                   = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
    fsm_state_next                      = fsm_state_reg;

    case (fsm_state_reg)

        SCR1_DBGC_FSM_STATE_IDLE : begin
            fsm_state_ready         = 1'b1;
            if (~state_lock_reg) begin
                fsm_ddr_input_sel   = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
            end
            else begin
                fsm_ddr_input_sel   = SCR1_DBGC_FSM_DDR_IN_SEL_LOCK;
            end
            fsm_hart_cmd_reg_wr     = state_hart_rst_exit_brk_req;
            if (decod_dap_cmd_req) begin
                fsm_state_next      = SCR1_DBGC_FSM_STATE_CMD_INT;
                fsm_opcode_reg_wr   = 1'b1;
                fsm_sampling_wr     = 1'b1;
                if (~decod_dap_update_dst_sel) begin
                    fsm_ddr_wr      = 1'b1;
                end
                else begin
                    fsm_dcir_wr     = 1'b1;
                end
            end
        end

        SCR1_DBGC_FSM_STATE_CMD_INT : begin
            fsm_ddr_input_sel               = SCR1_DBGC_FSM_DDR_IN_SEL_DBGC;
            case (decod_fsm_opcode_reg)

                SCR1_DBGC_FSM_OPCODE_REGTRANS : begin
                    fsm_state_next          = SCR1_DBGC_FSM_STATE_IDLE;
                    fsm_regblock_wr         = 1'b1;
                    fsm_hart_cmd_reg_wr     = state_hart_rst_exit_brk_req;
                end

                SCR1_DBGC_FSM_OPCODE_DBGCTRL : begin
                    fsm_regblock_wr         = 1'b1; // For Sticky Bits clearing
                    if (decod_hart_dbg_cmd_req) begin
                        fsm_state_next      = SCR1_DBGC_FSM_STATE_CMD_EXT;
                        fsm_hart_cmd_reg_wr = 1'b1;
                    end
                    else begin
                        fsm_state_next      = SCR1_DBGC_FSM_STATE_IDLE;
                        fsm_hart_cmd_reg_wr = state_hart_rst_exit_brk_req;
                    end
                end

                SCR1_DBGC_FSM_OPCODE_CORE_EXEC : begin
                    fsm_regblock_wr         = 1'b1;
                    case (state_dmode_reg)
                        SCR1_DBGC_HART_RUN_MODE : begin
                            fsm_hart_cmd_err_illeg_dbg_context  = 1'b1;
                            fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                        end
                        SCR1_DBGC_HART_DBG_MODE : begin
                            if (~hart_rst_sts) begin
                                fsm_hart_cmd_reg_wr             = 1'b1;
                                fsm_state_next                  = SCR1_DBGC_FSM_STATE_CMD_EXT;
                            end
                            else begin
                                fsm_hart_cmd_err_unexp_reset    = 1'b1;
                                fsm_hart_cmd_reg_wr             = state_hart_rst_exit_brk_req;
                                fsm_state_next                  = SCR1_DBGC_FSM_STATE_IDLE;
                            end
                        end
                        default : begin
                            fsm_hart_cmd_err_unexp_reset        = 1'b0;
                            fsm_hart_cmd_reg_wr                 = 1'b0;
                            fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                        end
                    endcase
                end

                SCR1_DBGC_FSM_OPCODE_UNLOCK : begin
                    fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                end
                default : begin
                    fsm_state_ready                     = 1'b0;
                    fsm_opcode_reg_wr                   = 1'b0;
                    fsm_ddr_wr                          = 1'b0;
                    fsm_dcir_wr                         = 1'b0;
                    fsm_regblock_wr                     = 1'b0;
                    fsm_sampling_wr                     = 1'b0;
                    fsm_except_lock_set                 = 1'b0;
                    fsm_hart_cmd_req                    = 1'b0;
                    fsm_hart_cmd_reg_wr                 = 1'b0;
                    fsm_hart_cmd_dmode_entr             = 1'b0;
                    fsm_hart_cmd_dmode_exit             = 1'b0;
                    fsm_hart_cmd_err_nack               = 1'b0;
                    fsm_hart_cmd_err_timeout            = 1'b0;
                    fsm_hart_cmd_err_illeg_dbg_context  = 1'b0;
                    fsm_hart_cmd_err_unexp_reset        = 1'b0;
                    fsm_ddr_input_sel                   = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
                    fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                end
            endcase
        end

        SCR1_DBGC_FSM_STATE_CMD_EXT : begin
            case (decod_fsm_opcode_reg)

                SCR1_DBGC_FSM_OPCODE_DBGCTRL : begin
                    fsm_hart_cmd_req                    = 1'b1;
                    if (~hart_rst_sts) begin
                        if (hart_dbg_cmd_nack) begin
                            fsm_hart_cmd_err_nack       = 1'b1;
                            fsm_hart_cmd_err_timeout    = hart_dbg_state.timeout;
                            fsm_state_next              = SCR1_DBGC_FSM_STATE_IDLE;
                        end
                        else begin
                            if (hart_dbg_cmd_ack) begin
                                fsm_state_next          = SCR1_DBGC_FSM_STATE_WAIT_EXT;
                            end
                        end
                    end
                    else begin
                        fsm_state_next                  = SCR1_DBGC_FSM_STATE_WAIT_EXT;
                    end
                end

                SCR1_DBGC_FSM_OPCODE_CORE_EXEC : begin
                    fsm_hart_cmd_req                = 1'b1;
                    if (~hart_rst_sts) begin
                        if (hart_dbg_cmd_nack) begin
                            fsm_hart_cmd_err_nack   = 1'b1;
                            fsm_state_next          = SCR1_DBGC_FSM_STATE_IDLE;
                        end
                        else begin
                            if (hart_dbg_cmd_ack) begin
                                fsm_state_next      = SCR1_DBGC_FSM_STATE_WAIT_EXT;
                            end
                        end
                    end
                    else begin
                        fsm_hart_cmd_err_unexp_reset    = 1'b1;
                        fsm_hart_cmd_reg_wr             = state_hart_rst_exit_brk_req;
                        fsm_state_next                  = SCR1_DBGC_FSM_STATE_IDLE;
                    end
                end

                default : begin
                    fsm_state_ready                     = 1'b0;
                    fsm_opcode_reg_wr                   = 1'b0;
                    fsm_ddr_wr                          = 1'b0;
                    fsm_dcir_wr                         = 1'b0;
                    fsm_regblock_wr                     = 1'b0;
                    fsm_sampling_wr                     = 1'b0;
                    fsm_except_lock_set                 = 1'b0;
                    fsm_hart_cmd_req                    = 1'b0;
                    fsm_hart_cmd_reg_wr                 = 1'b0;
                    fsm_hart_cmd_dmode_entr             = 1'b0;
                    fsm_hart_cmd_dmode_exit             = 1'b0;
                    fsm_hart_cmd_err_nack               = 1'b0;
                    fsm_hart_cmd_err_timeout            = 1'b0;
                    fsm_hart_cmd_err_illeg_dbg_context  = 1'b0;
                    fsm_hart_cmd_err_unexp_reset        = 1'b0;
                    fsm_ddr_input_sel                   = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
                    fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                end
            endcase
        end

        SCR1_DBGC_FSM_STATE_WAIT_EXT : begin
            fsm_ddr_input_sel                           = SCR1_DBGC_FSM_DDR_IN_SEL_CORE;
            case (decod_fsm_opcode_reg)

                SCR1_DBGC_FSM_OPCODE_DBGCTRL : begin
                    if (~hart_rst_sts) begin
                        if (hart_if_dbg_cmd_reg == SCR1_DBGC_HART_DBG_MODE) begin
                            if (hart_dbg_state.halted) begin
                                fsm_state_next          = SCR1_DBGC_FSM_STATE_IDLE;
                            end
                        end
                        else begin
                            if (~hart_dbg_state.halted) begin
                                fsm_state_next          = SCR1_DBGC_FSM_STATE_IDLE;
                            end
                        end
                    end
                    else begin
                        if (hart_if_dbg_cmd_reg == SCR1_DBGC_HART_DBG_MODE) begin
                            fsm_hart_cmd_dmode_entr     = 1'b1;
                            fsm_state_next              = SCR1_DBGC_FSM_STATE_IDLE;
                        end
                        else begin
                            if (~hart_dbg_state.halted) begin
                                fsm_hart_cmd_dmode_exit = 1'b1;
                                fsm_state_next          = SCR1_DBGC_FSM_STATE_IDLE;
                            end
                        end
                    end
                end

                SCR1_DBGC_FSM_OPCODE_CORE_EXEC : begin
                    if (~hart_rst_sts) begin
                        if (hart_dbg_state.halted) begin
                            fsm_state_next              = SCR1_DBGC_FSM_STATE_IDLE;
                            fsm_except_lock_set         = hart_dbg_state.except;
                        end
                    end
                    else begin
                        fsm_hart_cmd_err_unexp_reset    = 1'b1;
                        fsm_hart_cmd_reg_wr             = state_hart_rst_exit_brk_req;
                        fsm_state_next                  = SCR1_DBGC_FSM_STATE_IDLE;
                    end
                end

                default : begin
                    fsm_state_ready                     = 1'b0;
                    fsm_opcode_reg_wr                   = 1'b0;
                    fsm_ddr_wr                          = 1'b0;
                    fsm_dcir_wr                         = 1'b0;
                    fsm_regblock_wr                     = 1'b0;
                    fsm_sampling_wr                     = 1'b0;
                    fsm_except_lock_set                 = 1'b0;
                    fsm_hart_cmd_req                    = 1'b0;
                    fsm_hart_cmd_reg_wr                 = 1'b0;
                    fsm_hart_cmd_dmode_entr             = 1'b0;
                    fsm_hart_cmd_dmode_exit             = 1'b0;
                    fsm_hart_cmd_err_nack               = 1'b0;
                    fsm_hart_cmd_err_timeout            = 1'b0;
                    fsm_hart_cmd_err_illeg_dbg_context  = 1'b0;
                    fsm_hart_cmd_err_unexp_reset        = 1'b0;
                    fsm_ddr_input_sel                   = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
                    fsm_state_next                      = SCR1_DBGC_FSM_STATE_IDLE;
                end
            endcase
        end
        default : begin
            fsm_state_ready                             = 1'b0;
            fsm_opcode_reg_wr                           = 1'b0;
            fsm_ddr_wr                                  = 1'b0;
            fsm_dcir_wr                                 = 1'b0;
            fsm_regblock_wr                             = 1'b0;
            fsm_sampling_wr                             = 1'b0;
            fsm_except_lock_set                         = 1'b0;
            fsm_hart_cmd_req                            = 1'b0;
            fsm_hart_cmd_reg_wr                         = 1'b0;
            fsm_hart_cmd_dmode_entr                     = 1'b0;
            fsm_hart_cmd_dmode_exit                     = 1'b0;
            fsm_hart_cmd_err_nack                       = 1'b0;
            fsm_hart_cmd_err_timeout                    = 1'b0;
            fsm_hart_cmd_err_illeg_dbg_context          = 1'b0;
            fsm_hart_cmd_err_unexp_reset                = 1'b0;
            fsm_ddr_input_sel                           = SCR1_DBGC_FSM_DDR_IN_SEL_DAP;
            fsm_state_next                              = SCR1_DBGC_FSM_STATE_IDLE;
        end
    endcase
end

//-------------------------------------------------------------------------------
// Debug Controller's State signals
//-------------------------------------------------------------------------------

assign state_lock_set = state_core_err_posedge | fsm_except_lock_set;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        state_lock_reg      <= 1'b0;
    end
    else begin
        if (dap_lock_clr) begin
            state_lock_reg  <= 1'b0;
        end
        else if (state_lock_set) begin
            state_lock_reg  <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        state_dmode_reg     <= SCR1_DBGC_HART_RUN_MODE;
    end
    else begin
        if (state_dmode_clr) begin
            state_dmode_reg <= SCR1_DBGC_HART_RUN_MODE;
        end
        else if (state_dmode_set) begin
            state_dmode_reg <= SCR1_DBGC_HART_DBG_MODE;
        end
    end
end

always_comb begin
    state_dmode_clr                             = 1'b0;
    state_dmode_set                             = 1'b0;
    state_hart_rst_exit_brk_req                 = 1'b0;
    state_hart_dmode_cause_rst_entr             = 1'b0;

    case (state_dmode_reg)
        SCR1_DBGC_HART_RUN_MODE : begin
            if (fsm_hart_cmd_dmode_entr) begin
                state_dmode_set                 = 1'b1;
                state_hart_dmode_cause_rst_entr = 1'b1;
            end
            else begin
                if (hart_dbg_state.halted == SCR1_DBGC_HART_DBG_MODE) begin
                    state_dmode_set             = 1'b1;
                end
            end
        end
        SCR1_DBGC_HART_DBG_MODE : begin
            if (~hart_rst_sts) begin
                if (hart_dbg_state.halted == SCR1_DBGC_HART_RUN_MODE) begin
                    state_dmode_clr             = 1'b1;
                end
            end
            else begin
                if (fsm_hart_cmd_dmode_exit) begin
                    state_dmode_clr             = 1'b1;
                end
                else begin
                    state_hart_rst_exit_brk_req = state_hart_rst_posedge;
                end
            end
        end
        default : begin
            state_dmode_clr                     = 1'b0;
            state_dmode_set                     = 1'b0;
            state_hart_rst_exit_brk_req         = 1'b0;
            state_hart_dmode_cause_rst_entr     = 1'b0;
        end
    endcase
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        state_hart_dmode_cause_rst_entr_reg     <= 1'b0;
    end
    else begin
        if (state_dmode_clr) begin
            state_hart_dmode_cause_rst_entr_reg <= 1'b0;
        end
        else if (state_hart_dmode_cause_rst_entr) begin
            state_hart_dmode_cause_rst_entr_reg <= 1'b1;
        end
    end
end

assign state_hart_err_hwthread  = hart_dbg_state.error
                                & (state_dmode_reg == SCR1_DBGC_HART_DBG_MODE);

assign state_hart_err           = state_hart_err_hwthread
                                | hart_if_cmd_err_timeout_reg
                                | decod_err_invld_dap_opcode_hart_reg
                                | hart_if_cmd_err_nack_reg
                                | hart_if_cmd_err_illeg_dbg_context_reg
                                | hart_if_cmd_err_unexp_reset_reg;

assign state_core_err           = state_hart_err
                                | dap_err_fsm_busy_reg
                                |decod_err_invld_dap_opcode_core_reg;

assign state_hart_except        = hart_dbg_state.except
                                & (state_dmode_reg == SCR1_DBGC_HART_DBG_MODE);

assign state_hart_dmode_cause   = (state_dmode_reg == SCR1_DBGC_HART_DBG_MODE)
                                ? ( (hart_dbg_state.halted == SCR1_DBGC_HART_DBG_MODE)
                                    ? hart_dbg_state.dmode_cause
                                    : '0)
                                : '0;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        state_hart_err_delay <= 1'b0;
        state_core_err_delay <= 1'b0;
        state_core_rst_delay <= 1'b0;
        state_hart_rst_delay <= 1'b0;
    end
    else begin
        state_hart_err_delay <= state_hart_err;
        state_core_err_delay <= state_core_err;
        state_core_rst_delay <= core_rst_sts;
        state_hart_rst_delay <= hart_rst_sts;
    end
end

assign state_hart_err_posedge = state_hart_err & (~state_hart_err_delay);
assign state_core_err_posedge = state_core_err & (~state_core_err_delay);
assign state_core_rst_posedge = core_rst_sts & (~state_core_rst_delay);
assign state_hart_rst_posedge = hart_rst_sts & (~state_hart_rst_delay);

//-------------------------------------------------------------------------------
// Core Debug Control Register (CORE_DBG_CTRL, CDCR)
//-------------------------------------------------------------------------------
always_comb begin
    core_dcr_in                = hart_ddr_reg;

    core_dcr_out               = '0;
    core_dcr_out.rst           = core_dcr_core_rst_reg;
    core_dcr_out.irq_dsbl      = core_dcr_irq_dsbl_reg;
    core_dcr_out.hart[0].rst   = core_dcr_hart0_rst_reg;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        core_dcr_core_rst_reg  <= 1'b0;
        core_dcr_irq_dsbl_reg  <= SCR1_DBGC_HART_IRQ_DSBL_NORMAL;
        core_dcr_hart0_rst_reg <= 1'b0;
    end
    else begin
        if (decod_core_reg_wr.ctrl) begin
            core_dcr_core_rst_reg           <= core_dcr_in.rst;
            case (core_dcr_in.irq_dsbl)
                SCR1_DBGC_HART_IRQ_DSBL_NORMAL : begin
                    core_dcr_irq_dsbl_reg   <= SCR1_DBGC_HART_IRQ_DSBL_NORMAL;
                end
                SCR1_DBGC_HART_IRQ_DSBL_ACTIVE : begin
                    core_dcr_irq_dsbl_reg   <= SCR1_DBGC_HART_IRQ_DSBL_ACTIVE;
                end
                default : begin
                    core_dcr_irq_dsbl_reg   <= SCR1_DBGC_HART_IRQ_DSBL_NORMAL;
                end
            endcase
            core_dcr_hart0_rst_reg          <= core_dcr_in.hart[0].rst;
        end
    end
end

//-------------------------------------------------------------------------------
// Core Debug Status Register (CORE_DBG_STS, CDSR)
//-------------------------------------------------------------------------------
always_comb begin
    core_dsr_in                        = hart_ddr_reg;

    core_dsr_out                       = '0;
    core_dsr_out.lock                  = state_lock_reg;
    core_dsr_out.ready                 = fsm_state_ready;
    core_dsr_out.rst_sticky            = core_dsr_rst_stky_reg;
    core_dsr_out.rst                   = core_rst_sts;
    core_dsr_out.err                   = state_core_err;
    core_dsr_out.err_sticky            = core_dsr_err_stky_reg;
    core_dsr_out.err_hwcore            = state_hart_err_hwthread;
    core_dsr_out.err_fsm_busy          = dap_err_fsm_busy_reg;
    core_dsr_out.err_dap_opcode        = decod_err_invld_dap_opcode_core_reg;
    core_dsr_out.hart[0].dmode         = state_dmode_reg;
    core_dsr_out.hart[0].rst           = core_rst_sts;
    core_dsr_out.hart[0].rst_sticky    = core_dsr_rst_stky_reg;
    core_dsr_out.hart[0].err           = state_hart_err;
    core_dsr_out.hart[0].err_sticky    = core_dsr_hart0_err_stky_reg;
    core_dsr_out.hart[0].plvl          = 2'b11;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        core_dsr_rst_stky_reg       <= 1'b0;
    end
    else begin
        if (  (decod_core_reg_wr.sts )
            & (core_dsr_in.rst_sticky)
        ) begin
            core_dsr_rst_stky_reg   <= 1'b0;
        end
        else if (state_core_rst_posedge) begin
            core_dsr_rst_stky_reg   <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        core_dsr_err_stky_reg       <= 1'b0;
    end
    else begin
        if (  (decod_core_reg_wr.sts )
            & (core_dsr_in.err_sticky)
        ) begin
            core_dsr_err_stky_reg   <= 1'b0;
        end
        else if (state_core_err_posedge) begin
            core_dsr_err_stky_reg   <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        core_dsr_hart0_err_stky_reg     <= 1'b0;
    end
    else begin
        if (  (decod_core_reg_wr.sts )
            & (core_dsr_in.hart[0].err_sticky)
        ) begin
            core_dsr_hart0_err_stky_reg <= 1'b0;
        end
        else if (state_hart_err_posedge) begin
            core_dsr_hart0_err_stky_reg <= 1'b1;
        end
    end
end

//-------------------------------------------------------------------------------
// Core Debug Pipeline Status Register (CORE_DBG_PIPE_STS, CDPSR)
//-------------------------------------------------------------------------------
always_comb begin
    core_dpsr_out                       = '0;
    core_dpsr_out.busy.ifetch           = core_state_busy.ifetch;
    core_dpsr_out.busy.id               = core_state_busy.id;
    core_dpsr_out.busy.cfu              = core_state_busy.cfu;
    core_dpsr_out.busy.lsu              = core_state_busy.lsu;
    core_dpsr_out.busy.ialu             = core_state_busy.ialu;
`ifdef SCR1_RVM_EXT
    core_dpsr_out.busy.mdu              = core_state_busy.mdu;
`endif //SCR1_RVM_EXT
`ifdef SCR1_RVF_EXT
    core_dpsr_out.busy.fpu              = core_state_busy.fpu;
`endif //SCR1_RVF_EXT
    core_dpsr_out.busy.wb_cnt           = core_state_busy.wb_cnt;
end

//-------------------------------------------------------------------------------
// Hart Debug Control Register (HART_DBG_CTRL, HDCR)
//-------------------------------------------------------------------------------
always_comb begin
    hart_dcr_in                         = hart_ddr_reg;

    hart_dcr_out                        = '0;
    hart_dcr_out.rst                    = hart_dcr_rst_reg;
    hart_dcr_out.pc_advmt_dsbl          = hart_dcr_pc_admt_dsbl_reg;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_dcr_rst_reg                <= 1'b0;
        hart_dcr_pc_admt_dsbl_reg       <= 1'b0;
    end
    else begin
        if (decod_hart_reg_wr.ctrl) begin
            hart_dcr_rst_reg            <= hart_dcr_in.rst;
            hart_dcr_pc_admt_dsbl_reg   <= hart_dcr_in.pc_advmt_dsbl;
        end
    end
end

//-------------------------------------------------------------------------------
// Hart Debug Status Register (HART_DBG_STS, HDSR)
//-------------------------------------------------------------------------------
always_comb begin
    hart_dsr_out                        = '0;
    hart_dsr_out.dmode                  = state_dmode_reg;
    hart_dsr_out.rst                    = hart_rst_sts;
    hart_dsr_out.rst_sticky             = hart_dsr_rst_stky_reg;
    hart_dsr_out.except                 = state_hart_except;
    hart_dsr_out.plvl                   = 2'b11;
    hart_dsr_out.err                    = state_hart_err;
    hart_dsr_out.err_hwthread           = state_hart_err_hwthread;
    hart_dsr_out.err_dap_opcode         = decod_err_invld_dap_opcode_hart_reg;
    hart_dsr_out.err_dbgcmd_nack        = hart_if_cmd_err_nack_reg;
    hart_dsr_out.err_illeg_dbg_context  = hart_if_cmd_err_illeg_dbg_context_reg;
    hart_dsr_out.err_unexp_reset        = hart_if_cmd_err_unexp_reset_reg;
    hart_dsr_out.err_timeout            = hart_if_cmd_err_timeout_reg;
    hart_dsr_out.lock_sticky            = hart_dsr_lock_stky_reg;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_dsr_rst_stky_reg       <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_dsr_rst_stky_reg   <= 1'b0;
        end
        else if (state_hart_rst_posedge) begin
            hart_dsr_rst_stky_reg   <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_dsr_lock_stky_reg      <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_dsr_lock_stky_reg  <= 1'b0;
        end
        else if (state_lock_set) begin
            hart_dsr_lock_stky_reg  <= 1'b1;
        end
    end
end

//-------------------------------------------------------------------------------
// Hart Debug Mode Enable Register (HART_DMODE_ENBL, HDMER)
//-------------------------------------------------------------------------------
always_comb begin
    hart_dmer_in                    = hart_ddr_reg;

    hart_dmer_out                   = '0;
    hart_dmer_out.rst_exit_brk      = hart_dmer_reg.rst_brk;
    hart_dmer_out.sstep             = hart_dmer_reg.sstep;
    hart_dmer_out.brkpt             = hart_dmer_reg.brkpt;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_dmer_reg <= '0;
    end
    else begin
        if (decod_hart_reg_wr.dmode_en) begin
            hart_dmer_reg.rst_brk   <= hart_dmer_in.rst_exit_brk;
            hart_dmer_reg.sstep     <= hart_dmer_in.sstep;
            hart_dmer_reg.brkpt     <= hart_dmer_in.brkpt;
        end
    end
end

//-------------------------------------------------------------------------------
// Hart Debug Mode Cause Register (HART_DMODE_CAUSE, HDMCR)
//-------------------------------------------------------------------------------
always_comb begin
    hart_dmcr_out                   = '0;
    hart_dmcr_out.enforce           = state_hart_dmode_cause.enforce;
    hart_dmcr_out.rst_exit_brk      = state_hart_dmode_cause.rst_brk;
    hart_dmcr_out.rst_entr_brk      = state_hart_dmode_cause_rst_entr_reg;
    hart_dmcr_out.sstep             = state_hart_dmode_cause.sstep;
    hart_dmcr_out.brkpt             = state_hart_dmode_cause.brkpt;
    hart_dmcr_out.brkpt_hw          = state_hart_dmode_cause.brkpt_hw;
end

//-------------------------------------------------------------------------------
// Hart Debug Data Register (HART_DBG_DATA_REG, HDDR)
//-------------------------------------------------------------------------------

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_ddr_reg                <= '0;
    end
    else begin
        case (fsm_ddr_input_sel)

            SCR1_DBGC_FSM_DDR_IN_SEL_DAP : begin
                if (fsm_ddr_wr) begin
                    hart_ddr_reg    <= dap_data_shift_reg_pdout;
                end
            end

            SCR1_DBGC_FSM_DDR_IN_SEL_DBGC : begin
                if (decod_hart_reg_wr.ddr) begin
                    hart_ddr_reg    <= decod_ddr_mux;
                end
            end

            SCR1_DBGC_FSM_DDR_IN_SEL_CORE : begin
                if (hart_dbg_dreg_wr) begin
                    hart_ddr_reg    <= hart_dbg_dreg_in;
                end
            end

            SCR1_DBGC_FSM_DDR_IN_SEL_LOCK : begin
                if (dap_lock_clr) begin
                    hart_ddr_reg    <= decod_lock_context;
                end
            end
            default : begin
                hart_ddr_reg    <= '0;
            end
        endcase
    end
end

//-------------------------------------------------------------------------------
// Hart Debug Core Instruction Register (HART_DBG_CORE_INSTR_REG, HDCIR)
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_dcir_reg       <= '0;
    end
    else begin
        if (fsm_dcir_wr) begin
            hart_dcir_reg   <= dap_data_shift_reg_pdout;
        end
        else if (decod_hart_reg_wr.dcir) begin
            hart_dcir_reg   <= hart_ddr_reg;
        end
    end
end

//-------------------------------------------------------------------------------
// Hart Debug PC Sample Register (HART_DBG_PC_SAMPLE_REG, HDPCSR)
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_pcsample_reg       <= '0;
    end
    else begin
        if (decod_hart_pc_sample_reg_wr) begin
            hart_pcsample_reg   <= hart_dbg_pcsample;
        end
    end
end

//-------------------------------------------------------------------------------
// Core Debug I/F
//-------------------------------------------------------------------------------
assign core_if_rst_ctrl = core_dcr_core_rst_reg;
assign hart_if_rst_ctrl = core_if_rst_ctrl | core_dcr_hart0_rst_reg | hart_dcr_rst_reg;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_if_dbg_cmd_reg                 <= SCR1_DBGC_HART_RUN_MODE;
        hart_if_runctrl_reg.irq_dsbl        <= SCR1_DBGC_HART_IRQ_DSBL_NORMAL;
        hart_if_runctrl_reg.fetch_src       <= SCR1_DBGC_HART_FETCH_SRC_NORMAL;
        hart_if_runctrl_reg.dmode_en        <= '0;
        hart_if_runctrl_reg.pc_advmt_dsbl   <= 1'b0;
        hart_if_runctrl_reg.brkpt_hw_dsbl   <= 1'b0;
    end
    else begin
        if (fsm_hart_cmd_reg_wr) begin
            hart_if_dbg_cmd_reg             <= decod_hart_dbg_cmd;
            hart_if_runctrl_reg             <= decod_hart_runctrl;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_if_cmd_err_nack_reg        <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_if_cmd_err_nack_reg    <= 1'b0;
        end
        else if (fsm_hart_cmd_err_nack) begin
            hart_if_cmd_err_nack_reg    <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_if_cmd_err_timeout_reg     <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_if_cmd_err_timeout_reg <= 1'b0;
        end
        else if (fsm_hart_cmd_err_timeout) begin
            hart_if_cmd_err_timeout_reg <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_if_cmd_err_illeg_dbg_context_reg       <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_if_cmd_err_illeg_dbg_context_reg   <= 1'b0;
        end
        else if (fsm_hart_cmd_err_illeg_dbg_context) begin
            hart_if_cmd_err_illeg_dbg_context_reg   <= 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_if_cmd_err_unexp_reset_reg     <= 1'b0;
    end
    else begin
        if (decod_hart_sticky_clr) begin
            hart_if_cmd_err_unexp_reset_reg <= 1'b0;
        end
        else if (fsm_hart_cmd_err_unexp_reset) begin
            hart_if_cmd_err_unexp_reset_reg <= 1'b1;
        end
    end
end

assign core_rst_ctrl        = core_if_rst_ctrl;
assign hart_rst_ctrl        = hart_if_rst_ctrl;
assign hart_dbg_cmd         = hart_if_dbg_cmd_reg;
assign hart_dbg_cmd_req     = fsm_hart_cmd_req;
assign hart_dbg_runctrl     = hart_if_runctrl_reg;
assign hart_dbg_instr       = hart_dcir_reg;
assign hart_dbg_dreg_out    = hart_ddr_reg;

//-------------------------------------------------------------------------------
// Sleep logic
//-------------------------------------------------------------------------------
`ifdef SCR1_CLKCTRL_EN
assign sleep_rdy    = ~dap_ch_sel & (fsm_state_reg == SCR1_DBGC_FSM_STATE_IDLE);
assign sleep_wakeup =  dap_ch_sel | (~rst_n) | core_rst_sts | hart_rst_sts;
`endif // SCR1_CLKCTRL_EN

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_DBGC_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({
        fuse_mhartid,
        dap_ch_sel,
        dap_ch_id,
        dap_ch_capture,
        dap_ch_shift,
        dap_ch_update,
        dap_ch_tdi,
        core_rst_sts,
        core_state_busy,
        hart_rst_sts,
        hart_dbg_cmd_ack,
        hart_dbg_cmd_nack,
        hart_dbg_state,
        hart_dbg_dreg_in,
        hart_dbg_dreg_wr,
        hart_dbg_pcsample
    })
) else begin
    $error("DBGC error: unknown values");
end
`endif // SCR1_SIM_ENV

endmodule : scr1_dbgc

`endif // SCR1_DBGC_EN
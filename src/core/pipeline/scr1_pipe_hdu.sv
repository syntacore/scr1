/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_pipe_hdu.sv>
/// @brief      HART Debug Unit (HDU)
///

//------------------------------------------------------------------------------
 //
 //
 // Functionality:
 // - Controls HART state (RUN, Debug RUN, Debug HALTED)
 // - Setups Debug Mode execution
 // - Provides status information about Debug Mode execution
 // - Provides Program Buffer functionality (a few instructions execution while
 //   in Debug Mode)
 // - Provides access to Debug CSRs
 //
 // Structure:
 // - Debug state FSM
 // - HART Control logic
 // - HART Status logic
 // - Program Buffer
 // - Debug CSRs
 // - HDU <-> DM interface
 // - HDU <-> EXU interface
 // - HDU <-> IFU interface
 // - HDU <-> CSR interface
 // - HDU <-> TDU interface
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_hdu.svh"

module scr1_pipe_hdu #(parameter HART_PBUF_INSTR_REGOUT_EN = 1'b1) (
    // Common signals
    input  logic                                        rst_n,                      // HDU reset
    input  logic                                        clk,                        // HDU clock
    input  logic                                        clk_en,                     // HDU clock enable
`ifdef SCR1_CLKCTRL_EN
    input   logic                                       clk_pipe_en,                // Pipeline clock enable
`endif // SCR1_CLKCTRL_EN
    input  logic                                        pipe2hdu_rdc_qlfy_i,        // Pipeline RDC qualifier

    // HDU <-> CSR i/f
    input  logic                                        csr2hdu_req_i,              // CSR i/f request
    input  type_scr1_csr_cmd_sel_e                      csr2hdu_cmd_i,              // CSR i/f command
    input  logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]     csr2hdu_addr_i,             // CSR i/f address
    input  logic [`SCR1_XLEN-1:0]                       csr2hdu_wdata_i,            // CSR i/f write data
    output type_scr1_csr_resp_e                         hdu2csr_resp_o,             // CSR i/f response
    output logic [`SCR1_XLEN-1:0]                       hdu2csr_rdata_o,            // CSR i/f read data

    // HDU <-> DM i/f
    // HART Run Control i/f
    input  logic                                        dm2hdu_cmd_req_i,           // DM-HART Command request
    input  type_scr1_hdu_dbgstates_e                    dm2hdu_cmd_i,               // DM-HART Command
    output logic                                        hdu2dm_cmd_resp_o,          // DM-HART Command response
    output logic                                        hdu2dm_cmd_rcode_o,         // DM-HART Command return code: 0 - Ok; 1 - Error
    output logic                                        hdu2dm_hart_event_o,        // DM-HART Event: 1 if HART debug state changed
    output type_scr1_hdu_hartstatus_s                   hdu2dm_hart_status_o,       // DM-HART Status

    // Program Buffer i/f
    output logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]         hdu2dm_pbuf_addr_o,         // Program Buffer address - so far request only for 1 instruction
    input  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]        dm2hdu_pbuf_instr_i,        // Program Buffer instruction

    // HART Abstract Data regs i/f
    output logic                                        hdu2dm_dreg_req_o,          // Abstract Data Register request
    output logic                                        hdu2dm_dreg_wr_o,           // Abstract Data Register write
    output logic [`SCR1_XLEN-1:0]                       hdu2dm_dreg_wdata_o,        // Abstract Data Register write data
    input  logic                                        dm2hdu_dreg_resp_i,         // Abstract Data Register response
    input  logic                                        dm2hdu_dreg_fail_i,         // Abstract Data Register fail
    input  logic [`SCR1_XLEN-1:0]                       dm2hdu_dreg_rdata_i,        // Abstract Data Register read data

`ifdef SCR1_TDU_EN
    // HDU <-> TDU interface
    output  logic                                       hdu2tdu_hwbrk_dsbl_o,       // Disables BRKM
    input   logic                                       tdu2hdu_dmode_req_i,        // Trigger Module requests transition to debug mode
    input   logic                                       exu2hdu_ibrkpt_hw_i,        // Hardware breakpoint on current instruction
`endif // SCR1_TDU_EN

    // HART Run Status
    input   logic                                       pipe2hdu_exu_busy_i,        // EXU busy
    input   logic                                       pipe2hdu_instret_i,         // Instruction retired (with or without exception)
    input   logic                                       pipe2hdu_init_pc_i,         // Reset exit

    // HART Halt Status
    input   logic                                       pipe2hdu_exu_exc_req_i,     // Exception request
    input   logic                                       pipe2hdu_brkpt_i,           // Software Breakpoint (EBREAK)

    // HDU <-> EXU i/f
    // HART Run Control
    output  logic                                       hdu2exu_pbuf_fetch_o,       // Fetch instruction from Program Buffer
    output  logic                                       hdu2exu_no_commit_o,        // Forbid instruction commitment
    output  logic                                       hdu2exu_irq_dsbl_o,         // Disable IRQ
    output  logic                                       hdu2exu_pc_advmt_dsbl_o,    // Forbid PC advancement
    output  logic                                       hdu2exu_dmode_sstep_en_o,   // Enable single-step

    // HART state
    output  logic                                       hdu2exu_dbg_halted_o,       // Debug halted state
    output  logic                                       hdu2exu_dbg_run2halt_o,     // Transition to debug halted state
    output  logic                                       hdu2exu_dbg_halt2run_o,     // Transition to run state
    output  logic                                       hdu2exu_dbg_run_start_o,    // First cycle of run state

    // PC interface
    input  logic [`SCR1_XLEN-1:0]                       pipe2hdu_pc_curr_i,         // Current PC
    output logic [`SCR1_XLEN-1:0]                       hdu2exu_dbg_new_pc_o,       // New PC for resume

    // HDU <-> IFU i/f
    // Program Buffer Instruction interface
    input   logic                                       ifu2hdu_pbuf_instr_rdy_i,   // Program Buffer Instruction i/f ready
    output  logic                                       hdu2ifu_pbuf_instr_vd_o,    // Program Buffer Instruction valid
    output  logic                                       hdu2ifu_pbuf_instr_err_o,   // Program Buffer Instruction i/f error
    output  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]       hdu2ifu_pbuf_instr_o        // Program Buffer Instruction itself
);

//------------------------------------------------------------------------------
// Local Parameters
//------------------------------------------------------------------------------

localparam int unsigned SCR1_HDU_TIMEOUT       = 64;       // must be power of 2
localparam int unsigned SCR1_HDU_TIMEOUT_WIDTH = $clog2(SCR1_HDU_TIMEOUT);

//------------------------------------------------------------------------------
// Local Signals
//------------------------------------------------------------------------------

// Debug FSM
//------------------------------------------------------------------------------

// FSM control signals
logic                                               dm_dhalt_req;
logic                                               dm_run_req;

logic                                               dm_cmd_run;
logic                                               dm_cmd_dhalted;
logic                                               dm_cmd_drun;

// Debug state FSM signals
type_scr1_hdu_dbgstates_e                           dbg_state;
type_scr1_hdu_dbgstates_e                           dbg_state_next;
logic                                               dbg_state_dhalted;
logic                                               dbg_state_drun;
logic                                               dbg_state_run;
logic                                               dbg_state_reset;

// FSM transition, update and event registers
logic                                               dfsm_trans;
logic                                               dfsm_trans_next;
logic                                               dfsm_update;
logic                                               dfsm_update_next;
logic                                               dfsm_event;
logic                                               dfsm_event_next;

// HART Control signals
//------------------------------------------------------------------------------

logic                                               hart_resume_req;
logic                                               hart_halt_req;
logic                                               hart_cmd_req;

// HART Run Control register
logic                                               hart_runctrl_upd;
logic                                               hart_runctrl_clr;
type_scr1_hdu_runctrl_s                             hart_runctrl;

// HART halt request timeout counter signals
logic [SCR1_HDU_TIMEOUT_WIDTH-1:0]                  halt_req_timeout_cnt;
logic [SCR1_HDU_TIMEOUT_WIDTH-1:0]                  halt_req_timeout_cnt_next;
logic                                               halt_req_timeout_cnt_en;
logic                                               halt_req_timeout_flag;

// HART Status signals
//------------------------------------------------------------------------------

type_scr1_hdu_haltstatus_s                          hart_haltstatus;
type_scr1_hdu_haltcause_e                           hart_haltcause;

logic                                               hart_halt_pnd;
logic                                               hart_halt_ack;

// Debug mode cause decoder signals
logic                                               dmode_cause_sstep;
logic                                               dmode_cause_except;
logic                                               dmode_cause_ebreak;
logic                                               dmode_cause_any;
`ifdef SCR1_TDU_EN
logic                                               dmode_cause_tmreq;
`endif // SCR1_TDU_EN

// Program Buffer FSM
//------------------------------------------------------------------------------

// PBUF FSM control signals
logic                                               ifu_handshake_done;
logic                                               pbuf_exc_inj_req;
logic                                               pbuf_exc_inj_end;
logic                                               pbuf_start_fetch;

// PBUF FSM signals
type_scr1_hdu_pbufstates_e                          pbuf_fsm_curr;
type_scr1_hdu_pbufstates_e                          pbuf_fsm_next;
logic                                               pbuf_fsm_idle;
logic                                               pbuf_fsm_fetch;
logic                                               pbuf_fsm_excinj;

// PBUF address signals
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]                pbuf_addr_ff;
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]                pbuf_addr_next;
logic                                               pbuf_addr_end;
logic                                               pbuf_addr_next_vd;

logic                                               pbuf_instr_wait_latching;

// Debugs CSRs
//------------------------------------------------------------------------------

// CSRs write/read interface signals
logic                                               csr_upd_on_halt;
logic                                               csr_wr;
logic [`SCR1_XLEN-1:0]                              csr_wr_data;
logic [`SCR1_XLEN-1:0]                              csr_rd_data;

// Debug Control and Status register (DCSR)
logic                                               csr_dcsr_sel;
logic                                               csr_dcsr_wr;
type_scr1_hdu_dcsr_s                                csr_dcsr_in;
type_scr1_hdu_dcsr_s                                csr_dcsr_out;
logic                                               csr_dcsr_ebreakm;
logic                                               csr_dcsr_stepie;
logic                                               csr_dcsr_step;
logic [SCR1_HDU_DCSR_CAUSE_BIT_L-
       SCR1_HDU_DCSR_CAUSE_BIT_R:0]                 csr_dcsr_cause;

// Debug Program Counter register (DPC)
logic                                               csr_dpc_sel;
logic                                               csr_dpc_wr;
logic [`SCR1_XLEN-1:0]                              csr_dpc_ff;
logic [`SCR1_XLEN-1:0]                              csr_dpc_next;
logic [`SCR1_XLEN-1:0]                              csr_dpc_out;

// Debug Scratch register 0 (DSCRATCH0)
logic                                               csr_addr_dscratch0;
logic                                               csr_dscratch0_sel;
logic                                               csr_dscratch0_wr;
logic [`SCR1_XLEN-1:0]                              csr_dscratch0_out;
type_scr1_csr_resp_e                                csr_dscratch0_resp;

//------------------------------------------------------------------------------
// Debug state FSM logic
//------------------------------------------------------------------------------
//
 // Debug state FSM logic consists of the following functional units:
 // - FSM control logic
 // - Debug state FSM
 // - FSM transition, update and event registers
//

// FSM control logic
//------------------------------------------------------------------------------

assign dm_cmd_dhalted = (dm2hdu_cmd_i == SCR1_HDU_DBGSTATE_DHALTED);
assign dm_cmd_run     = (dm2hdu_cmd_i == SCR1_HDU_DBGSTATE_RUN);
assign dm_cmd_drun    = (dm2hdu_cmd_i == SCR1_HDU_DBGSTATE_DRUN);

assign dm_dhalt_req   = dm2hdu_cmd_req_i & dm_cmd_dhalted;
assign dm_run_req     = dm2hdu_cmd_req_i & (dm_cmd_run | dm_cmd_drun);

// Debug state FSM
//------------------------------------------------------------------------------

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dbg_state <= SCR1_HDU_DBGSTATE_RESET;
    end else begin
        dbg_state <= dbg_state_next;
    end
end

always_comb begin
    if (~pipe2hdu_rdc_qlfy_i) begin
        dbg_state_next = SCR1_HDU_DBGSTATE_RESET;
    end else begin
        case (dbg_state)
            SCR1_HDU_DBGSTATE_RESET: begin
                dbg_state_next = ~pipe2hdu_init_pc_i ? SCR1_HDU_DBGSTATE_RESET
                               : dm_dhalt_req        ? SCR1_HDU_DBGSTATE_DHALTED
                                                     : SCR1_HDU_DBGSTATE_RUN;
            end
            SCR1_HDU_DBGSTATE_RUN: begin
                dbg_state_next = dfsm_update         ? SCR1_HDU_DBGSTATE_DHALTED
                                                     : SCR1_HDU_DBGSTATE_RUN;
            end
            SCR1_HDU_DBGSTATE_DHALTED: begin
                dbg_state_next = ~dfsm_update        ? SCR1_HDU_DBGSTATE_DHALTED
                               : dm_cmd_drun         ? SCR1_HDU_DBGSTATE_DRUN
                                                     : SCR1_HDU_DBGSTATE_RUN;
            end
            SCR1_HDU_DBGSTATE_DRUN: begin
                dbg_state_next = dfsm_update         ? SCR1_HDU_DBGSTATE_DHALTED
                                                     : SCR1_HDU_DBGSTATE_DRUN;
            end
            default: begin
                dbg_state_next = SCR1_HDU_DBGSTATE_XXX;
            end
        endcase
    end
end

assign dbg_state_dhalted = (dbg_state == SCR1_HDU_DBGSTATE_DHALTED);
assign dbg_state_drun    = (dbg_state == SCR1_HDU_DBGSTATE_DRUN);
assign dbg_state_run     = (dbg_state == SCR1_HDU_DBGSTATE_RUN);
assign dbg_state_reset   = (dbg_state == SCR1_HDU_DBGSTATE_RESET);

// FSM transition, update and event registers
//------------------------------------------------------------------------------

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dfsm_trans  <= 1'b0;
        dfsm_update <= 1'b0;
        dfsm_event  <= 1'b0;
    end else begin
        dfsm_trans  <= dfsm_trans_next;
        dfsm_update <= dfsm_update_next;
        dfsm_event  <= dfsm_event_next;
    end
end

always_comb begin
    if (~pipe2hdu_rdc_qlfy_i) begin
        dfsm_trans_next  = 1'b0;
        dfsm_update_next = 1'b0;
        dfsm_event_next  = 1'b1;
    end else begin
        case (dbg_state)
            SCR1_HDU_DBGSTATE_RESET: begin
                dfsm_trans_next  = 1'b0;
                dfsm_update_next = 1'b0;
                dfsm_event_next  = pipe2hdu_init_pc_i & ~dm2hdu_cmd_req_i;
            end

            SCR1_HDU_DBGSTATE_RUN,
            SCR1_HDU_DBGSTATE_DRUN: begin
                dfsm_trans_next  = ~dfsm_update ? hart_halt_pnd : dfsm_trans;
                dfsm_update_next = ~dfsm_update & hart_halt_ack;
                dfsm_event_next  = dfsm_update;
            end

            SCR1_HDU_DBGSTATE_DHALTED: begin
                dfsm_trans_next  = ~dfsm_update ? ~dfsm_trans & dm_run_req
                                                : dfsm_trans;
                dfsm_update_next = ~dfsm_update & dfsm_trans;
                dfsm_event_next  = dfsm_update;
            end
        endcase
    end
end

//------------------------------------------------------------------------------
// HART Control logic
//------------------------------------------------------------------------------
//
 // HART Control logic consists of the following functional units:
 // - Control signals
 // - HART Run Control register
 // - HART Halt Request Time-Out counter
//

// Control logic
always_comb begin
    if (~pipe2hdu_rdc_qlfy_i) begin
        hart_cmd_req = 1'b0;
    end else begin
        case (dbg_state)
            SCR1_HDU_DBGSTATE_RESET  : hart_cmd_req = dm2hdu_cmd_req_i;
            SCR1_HDU_DBGSTATE_DHALTED: hart_cmd_req = (dfsm_update | dfsm_trans);
            SCR1_HDU_DBGSTATE_RUN,
            SCR1_HDU_DBGSTATE_DRUN   : hart_cmd_req = ~dfsm_update & dfsm_trans;
        endcase
    end
end

assign hart_halt_req   = dm_cmd_dhalted & hart_cmd_req;
assign hart_resume_req = (dm_cmd_run | dm_cmd_drun) & hart_cmd_req;

// HART Run Control register
//------------------------------------------------------------------------------

assign hart_runctrl_clr = (dbg_state_run | dbg_state_drun)
                        & (dbg_state_next == SCR1_HDU_DBGSTATE_DHALTED);
assign hart_runctrl_upd = dbg_state_dhalted & dfsm_trans_next;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        hart_runctrl.irq_dsbl      <= 1'b0;
        hart_runctrl.fetch_src     <= SCR1_HDU_FETCH_SRC_NORMAL;
        hart_runctrl.pc_advmt_dsbl <= 1'b0;
        hart_runctrl.hwbrkpt_dsbl  <= 1'b0;
        hart_runctrl.redirect      <= '0;
    end else if(clk_en) begin
        if (hart_runctrl_clr) begin
            hart_runctrl           <= '0;
        end else begin
            if (hart_runctrl_upd) begin
                if (~dm_cmd_drun) begin
                    // Case : resume to RUN state
                    hart_runctrl.irq_dsbl        <= csr_dcsr_step ? ~csr_dcsr_stepie : 1'b0;
                    hart_runctrl.fetch_src       <= SCR1_HDU_FETCH_SRC_NORMAL;
                    hart_runctrl.pc_advmt_dsbl   <= 1'b0;
                    hart_runctrl.hwbrkpt_dsbl    <= 1'b0;
                    hart_runctrl.redirect.sstep  <= csr_dcsr_step;
                    hart_runctrl.redirect.ebreak <= csr_dcsr_ebreakm;
                end else begin
                    // Case : resume to DRUN state
                    hart_runctrl.irq_dsbl        <= 1'b1;
                    hart_runctrl.fetch_src       <= SCR1_HDU_FETCH_SRC_PBUF;
                    hart_runctrl.pc_advmt_dsbl   <= 1'b1;
                    hart_runctrl.hwbrkpt_dsbl    <= 1'b1;
                    hart_runctrl.redirect.sstep  <= 1'b0;
                    hart_runctrl.redirect.ebreak <= 1'b1;
                end
            end
        end
    end
end

// HART Halt Request Time-Out counter
//------------------------------------------------------------------------------
// HART goes into halt state only if the halt request is present for timeout period
// of time

assign halt_req_timeout_cnt_en = hdu2exu_dbg_halt2run_o
                               | (hart_halt_req & ~hdu2exu_dbg_run2halt_o);

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        halt_req_timeout_cnt <= '1;
    end else if (halt_req_timeout_cnt_en) begin
        halt_req_timeout_cnt <= halt_req_timeout_cnt_next;
    end
end

assign halt_req_timeout_cnt_next = hdu2exu_dbg_halt2run_o                    ? '1
                                 : (hart_halt_req & ~hdu2exu_dbg_run2halt_o) ? halt_req_timeout_cnt - 1'b1
                                                                             : halt_req_timeout_cnt;

assign halt_req_timeout_flag = ~|halt_req_timeout_cnt;

//------------------------------------------------------------------------------
// HART Status logic
//------------------------------------------------------------------------------
//
 // HART Status logic consists of the following functional units:
 // - Debug mode cause decoder
 // - Hart halt status cause encoder
 // - Hart halt status register
//

// Debug mode cause decoder
//------------------------------------------------------------------------------

assign dmode_cause_sstep  = hart_runctrl.redirect.sstep & pipe2hdu_instret_i;
assign dmode_cause_except = dbg_state_drun & pipe2hdu_exu_exc_req_i
                          & ~pipe2hdu_brkpt_i
`ifdef SCR1_TDU_EN
                          & ~exu2hdu_ibrkpt_hw_i
`endif // SCR1_TDU_EN
                          ;
assign dmode_cause_ebreak = hart_runctrl.redirect.ebreak & pipe2hdu_brkpt_i;
`ifdef SCR1_TDU_EN
assign dmode_cause_tmreq  = tdu2hdu_dmode_req_i & exu2hdu_ibrkpt_hw_i;
`endif // SCR1_TDU_EN

assign dmode_cause_any = dmode_cause_sstep | dmode_cause_ebreak | dmode_cause_except
                       | hart_halt_req
`ifdef SCR1_TDU_EN
                       | dmode_cause_tmreq
`endif // SCR1_TDU_EN
                       ;

// HART halt cause encoder
//------------------------------------------------------------------------------

always_comb begin
    case (1'b1)
`ifdef SCR1_TDU_EN
        dmode_cause_tmreq   : hart_haltcause = SCR1_HDU_HALTCAUSE_TMREQ;
`endif // SCR1_TDU_EN
        dmode_cause_ebreak  : hart_haltcause = SCR1_HDU_HALTCAUSE_EBREAK;
        hart_halt_req       : hart_haltcause = SCR1_HDU_HALTCAUSE_DMREQ;
        dmode_cause_sstep   : hart_haltcause = SCR1_HDU_HALTCAUSE_SSTEP;
        default             : hart_haltcause = SCR1_HDU_HALTCAUSE_NONE;
    endcase
end

// HART halt status register
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        hart_haltstatus        <= '0;
    end else if (hart_halt_ack) begin
        hart_haltstatus.except <= dmode_cause_except;
        hart_haltstatus.cause  <= hart_haltcause;
    end
end

assign hart_halt_pnd = (dfsm_trans | dm_dhalt_req) & ~hart_halt_ack;
assign hart_halt_ack = ~hdu2exu_dbg_halted_o
                     & (halt_req_timeout_flag | (~pipe2hdu_exu_busy_i & dmode_cause_any));

//------------------------------------------------------------------------------
// Program Buffer (PBUF) logic
//------------------------------------------------------------------------------
//
 // Program Buffer allows to execute small programs in debug mode
//

// To terminate Program Buffer execution exception should be raised. There are 2
// cases:
// - One of PBUF instructions raise an exception
// - No PBUF instruction raise an exception before the last PBUF instruction has
// been issued. In this case FSM goes into EXCINJECT state and an "Instruction
// fetch access fault" exception is injected

// PBUF FSM
//------------------------------------------------------------------------------

assign ifu_handshake_done = hdu2ifu_pbuf_instr_vd_o & ifu2hdu_pbuf_instr_rdy_i;
assign pbuf_addr_end      = (pbuf_addr_ff == (SCR1_HDU_PBUF_ADDR_SPAN-1));

assign pbuf_start_fetch = dbg_state_dhalted      & (dbg_state_next == SCR1_HDU_DBGSTATE_DRUN);
assign pbuf_exc_inj_req = ifu_handshake_done     & pbuf_addr_end;
assign pbuf_exc_inj_end = pipe2hdu_exu_exc_req_i | ifu_handshake_done;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        pbuf_fsm_curr <= SCR1_HDU_PBUFSTATE_IDLE;
    end else if(clk_en) begin
        pbuf_fsm_curr <= pbuf_fsm_next;
    end
end

always_comb begin
    case (pbuf_fsm_curr)
        SCR1_HDU_PBUFSTATE_IDLE: begin
            pbuf_fsm_next = pbuf_start_fetch       ? SCR1_HDU_PBUFSTATE_FETCH
                                                   : SCR1_HDU_PBUFSTATE_IDLE;
        end
        SCR1_HDU_PBUFSTATE_FETCH: begin
            pbuf_fsm_next = pipe2hdu_exu_exc_req_i ? SCR1_HDU_PBUFSTATE_WAIT4END
                          : pbuf_exc_inj_req       ? SCR1_HDU_PBUFSTATE_EXCINJECT
                                                   : SCR1_HDU_PBUFSTATE_FETCH;
        end
        SCR1_HDU_PBUFSTATE_EXCINJECT: begin
            pbuf_fsm_next = pbuf_exc_inj_end       ? SCR1_HDU_PBUFSTATE_WAIT4END
                                                   : SCR1_HDU_PBUFSTATE_EXCINJECT;
        end
        SCR1_HDU_PBUFSTATE_WAIT4END: begin
            pbuf_fsm_next = hdu2exu_dbg_halted_o   ? SCR1_HDU_PBUFSTATE_IDLE
                                                   : SCR1_HDU_PBUFSTATE_WAIT4END;
        end
    endcase
end

assign pbuf_fsm_idle   = (pbuf_fsm_curr == SCR1_HDU_PBUFSTATE_IDLE);
assign pbuf_fsm_fetch  = (pbuf_fsm_curr == SCR1_HDU_PBUFSTATE_FETCH);
assign pbuf_fsm_excinj = (pbuf_fsm_curr == SCR1_HDU_PBUFSTATE_EXCINJECT);

// Program Buffer address register
//------------------------------------------------------------------------------

assign pbuf_addr_next_vd = pbuf_fsm_fetch          & ifu_handshake_done
                         & ~pipe2hdu_exu_exc_req_i & ~pbuf_addr_end;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        pbuf_addr_ff <= '0;
    end else if(clk_en) begin
        pbuf_addr_ff <= pbuf_addr_next;
    end
end

assign pbuf_addr_next = pbuf_fsm_idle     ? '0
                      : pbuf_addr_next_vd ? pbuf_addr_ff + 1'b1
                                          : pbuf_addr_ff;

// Pass instruction from debug program buffer to cpu pipeline with two options:
// - through register, better for frequency
// - through wires, better for area
generate if (HART_PBUF_INSTR_REGOUT_EN) begin
    always_ff @(posedge clk, negedge rst_n) begin
        if (~rst_n) begin
            pbuf_instr_wait_latching <= 1'b0;
        end else begin
            pbuf_instr_wait_latching <= ifu_handshake_done;
        end
    end
end else begin
    assign pbuf_instr_wait_latching = 1'b0;
end endgenerate

//------------------------------------------------------------------------------
// Debug CSRs
//------------------------------------------------------------------------------

assign csr_upd_on_halt = (dbg_state_reset | dbg_state_run)
                       & (dbg_state_next == SCR1_HDU_DBGSTATE_DHALTED);

// CSRs select logic
//------------------------------------------------------------------------------

always_comb begin : csr_if_regsel
    csr_dcsr_sel        = 1'b0;
    csr_dpc_sel         = 1'b0;
    csr_dscratch0_sel   = 1'b0;
    //csr_dscratch1_sel   = 1'b0;

    if (csr2hdu_req_i) begin
        case (csr2hdu_addr_i)
            SCR1_HDU_DBGCSR_OFFS_DCSR     : csr_dcsr_sel      = 1'b1;
            SCR1_HDU_DBGCSR_OFFS_DPC      : csr_dpc_sel       = 1'b1;
            SCR1_HDU_DBGCSR_OFFS_DSCRATCH0: csr_dscratch0_sel = 1'b1;
            default : begin
                                            csr_dcsr_sel      = 1'bX;
                                            csr_dpc_sel       = 1'bX;
                                            csr_dscratch0_sel = 1'bX;
            end
        endcase
    end
end : csr_if_regsel

// CSRs read interface
//------------------------------------------------------------------------------

assign csr_rd_data = csr_dcsr_out | csr_dpc_out | csr_dscratch0_out;

// CSRs write interface
//------------------------------------------------------------------------------

assign csr_wr = csr2hdu_req_i;

always_comb begin : csr_if_write
    csr_wr_data     = '0;

    if (csr2hdu_req_i) begin
        case (csr2hdu_cmd_i)
            SCR1_CSR_CMD_WRITE : csr_wr_data = csr2hdu_wdata_i;
            SCR1_CSR_CMD_SET   : csr_wr_data = csr_rd_data | csr2hdu_wdata_i;
            SCR1_CSR_CMD_CLEAR : csr_wr_data = csr_rd_data & (~csr2hdu_wdata_i);
            default            : csr_wr_data = 'X;
        endcase
    end
end : csr_if_write

// Debug Control and Status register
//------------------------------------------------------------------------------
// Setups the HART behaviour in Debug Mode and holds Debug status information

always_comb begin
    csr_dcsr_in                 = csr_wr_data;
    csr_dcsr_wr                 = csr_wr & csr_dcsr_sel;

    csr_dcsr_out                = '0;
    if (csr_dcsr_sel) begin
        csr_dcsr_out.xdebugver  = SCR1_HDU_DEBUGCSR_DCSR_XDEBUGVER;
        csr_dcsr_out.ebreakm    = csr_dcsr_ebreakm;
        csr_dcsr_out.stepie     = csr_dcsr_stepie;
        csr_dcsr_out.step       = csr_dcsr_step;
        csr_dcsr_out.prv        = 2'b11;
        csr_dcsr_out.cause      = csr_dcsr_cause;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_dcsr_ebreakm        <= 1'b0;
        csr_dcsr_stepie         <= 1'b0;
        csr_dcsr_step           <= 1'b0;
    end else if(clk_en) begin
        if (csr_dcsr_wr) begin
            csr_dcsr_ebreakm    <= csr_dcsr_in.ebreakm;
            csr_dcsr_stepie     <= csr_dcsr_in.stepie;
            csr_dcsr_step       <= csr_dcsr_in.step;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        csr_dcsr_cause <= 1'b0;
    end else if(clk_en) begin
        if(csr_upd_on_halt) begin
            csr_dcsr_cause <= hart_haltstatus.cause;
        end
    end
end

// Debug PC register
//------------------------------------------------------------------------------
// Saves the virtual address of the next instruction to be executed when Debug
// Mode is entered. Could be changed by debugger

assign csr_dpc_wr   = csr_wr & csr_dpc_sel;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        csr_dpc_ff <= '0;
    end else if(clk_en) begin
        csr_dpc_ff <= csr_dpc_next;
    end
end

assign csr_dpc_next = csr_upd_on_halt ? pipe2hdu_pc_curr_i
                    : csr_dpc_wr      ? csr_wr_data
                                      : csr_dpc_ff;
assign csr_dpc_out  = csr_dpc_sel     ? csr_dpc_ff : '0;

// Debug Scratch 0 register
//------------------------------------------------------------------------------

assign csr_dscratch0_resp = (~dm2hdu_dreg_resp_i | dm2hdu_dreg_fail_i)
                          ? SCR1_CSR_RESP_ER
                          : SCR1_CSR_RESP_OK;
assign csr_dscratch0_out  = csr_dscratch0_sel ? dm2hdu_dreg_rdata_i : '0;

//------------------------------------------------------------------------------
// HDU <-> DM interface
//------------------------------------------------------------------------------

assign hdu2dm_hart_event_o = dfsm_event;

// HART status
always_comb begin
    hdu2dm_hart_status_o           = '0;
    hdu2dm_hart_status_o.dbg_state = dbg_state;
    hdu2dm_hart_status_o.except    = dbg_state_dhalted & hart_haltstatus.except;
    hdu2dm_hart_status_o.ebreak    = dbg_state_dhalted & (hart_haltstatus.cause == SCR1_HDU_HALTCAUSE_EBREAK);
end

assign hdu2dm_cmd_rcode_o = dbg_state_reset
                          ? ~pipe2hdu_rdc_qlfy_i | ~pipe2hdu_init_pc_i | ~dm2hdu_cmd_req_i
                          : ~pipe2hdu_rdc_qlfy_i | ~dfsm_update;

always_comb begin
    case (dbg_state)
        SCR1_HDU_DBGSTATE_RESET: begin
            hdu2dm_cmd_resp_o  = pipe2hdu_rdc_qlfy_i & pipe2hdu_init_pc_i & dm2hdu_cmd_req_i;
        end

        SCR1_HDU_DBGSTATE_RUN: begin
            hdu2dm_cmd_resp_o  = pipe2hdu_rdc_qlfy_i & dfsm_update & dm2hdu_cmd_req_i;
        end

        SCR1_HDU_DBGSTATE_DHALTED: begin
            hdu2dm_cmd_resp_o  = pipe2hdu_rdc_qlfy_i ? dfsm_update : dm2hdu_cmd_req_i;
        end

        SCR1_HDU_DBGSTATE_DRUN: begin
            hdu2dm_cmd_resp_o  = (~pipe2hdu_rdc_qlfy_i | dfsm_update) & dm2hdu_cmd_req_i;
        end
    endcase
end

assign hdu2dm_pbuf_addr_o  = pbuf_addr_ff;
assign hdu2dm_dreg_req_o   = csr_dscratch0_sel;
assign hdu2dm_dreg_wr_o    = csr_wr & csr_dscratch0_sel;
assign hdu2dm_dreg_wdata_o = csr_wr_data;

//------------------------------------------------------------------------------
// HDU <-> EXU interface
//------------------------------------------------------------------------------

assign hdu2exu_dbg_halted_o    = (dbg_state_next == SCR1_HDU_DBGSTATE_DHALTED)
                               | (~pipe2hdu_rdc_qlfy_i & ~dbg_state_run);
assign hdu2exu_dbg_run_start_o = dbg_state_dhalted & pipe2hdu_rdc_qlfy_i & dfsm_update;
assign hdu2exu_dbg_halt2run_o  = hdu2exu_dbg_halted_o & hart_resume_req
`ifdef SCR1_CLKCTRL_EN
                               & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                               ;
assign hdu2exu_dbg_run2halt_o  = hart_halt_ack;

assign hdu2exu_pbuf_fetch_o    = hart_runctrl.fetch_src;
assign hdu2exu_irq_dsbl_o      = hart_runctrl.irq_dsbl;
assign hdu2exu_pc_advmt_dsbl_o = hart_runctrl.pc_advmt_dsbl;
// No change in arch. state if dmode caused by breakpoint
assign hdu2exu_no_commit_o     = dmode_cause_ebreak
`ifdef SCR1_TDU_EN
                               | dmode_cause_tmreq
`endif // SCR1_TDU_EN
                               ;
assign hdu2exu_dmode_sstep_en_o = hart_runctrl.redirect.sstep;
assign hdu2exu_dbg_new_pc_o     = csr_dpc_ff;

//------------------------------------------------------------------------------
// HDU <-> IFU interface
//------------------------------------------------------------------------------

assign hdu2ifu_pbuf_instr_vd_o  = (pbuf_fsm_fetch | pbuf_fsm_excinj)
                                & ~pbuf_instr_wait_latching;
assign hdu2ifu_pbuf_instr_err_o = pbuf_fsm_excinj;

generate if (HART_PBUF_INSTR_REGOUT_EN) begin
    always_ff @(posedge clk) begin
        hdu2ifu_pbuf_instr_o <= dm2hdu_pbuf_instr_i;
    end
end else begin
    assign hdu2ifu_pbuf_instr_o = dm2hdu_pbuf_instr_i;
end endgenerate

//------------------------------------------------------------------------------
// HDU <-> CSR interface
//------------------------------------------------------------------------------

assign csr_addr_dscratch0 = (csr2hdu_addr_i == SCR1_HDU_DBGCSR_OFFS_DSCRATCH0);

assign hdu2csr_resp_o  = ~dbg_state_drun    ? SCR1_CSR_RESP_ER
                       : csr_addr_dscratch0 ? csr_dscratch0_resp
                       : csr2hdu_req_i      ? SCR1_CSR_RESP_OK
                                            : SCR1_CSR_RESP_ER;
assign hdu2csr_rdata_o = csr_rd_data;

`ifdef SCR1_TDU_EN
//------------------------------------------------------------------------------
// HDU <-> TDU interface
//------------------------------------------------------------------------------

assign hdu2tdu_hwbrk_dsbl_o = hart_runctrl.hwbrkpt_dsbl;
`endif // SCR1_TDU_EN

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SVA_HDU_XCHECK_COMMON :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {rst_n,clk,clk_en,csr2hdu_req_i,pipe2hdu_rdc_qlfy_i} )
    )
    else $error("HDU Error: common signals are in X state");

SVA_HDU_XCHECK_CSR_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        csr2hdu_req_i |-> !$isunknown( {csr2hdu_cmd_i,csr2hdu_addr_i,csr2hdu_wdata_i} )
    )
    else $error("HDU Error: CSR i/f is in X state");

SVA_HDU_XCHECK_DM_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {dm2hdu_cmd_req_i,dm2hdu_cmd_i,dm2hdu_dreg_resp_i,
        dm2hdu_dreg_fail_i} )
    )
    else $error("HDU Error: DM i/f is in X state");

SVA_HDU_XCHECK_TDU_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {tdu2hdu_dmode_req_i,exu2hdu_ibrkpt_hw_i} )
    )
    else $error("HDU Error: TDU i/f is in X state");

SVA_HDU_XCHECK_HART_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {pipe2hdu_exu_busy_i,pipe2hdu_instret_i,pipe2hdu_init_pc_i,pipe2hdu_exu_exc_req_i,pipe2hdu_brkpt_i,
        pipe2hdu_pc_curr_i,ifu2hdu_pbuf_instr_rdy_i} )
    )
    else $error("HDU Error: HART i/f is in X state");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_hdu

`endif // SCR1_DBG_EN

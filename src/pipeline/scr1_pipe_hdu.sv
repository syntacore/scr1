/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_pipe_hdu.sv>
/// @brief      HART Debug Unit (HDU)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_arch_types.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_hdu.svh"


module scr1_pipe_hdu #( parameter HART_PBUF_INSTR_REGOUT_EN = 1'b1 ) (
    // Common signals
    input  logic                                            rst_n,          // HDU reset
    input  logic                                            clk,            // HDU clock
    input  logic                                            clk_en,         // HDU clock enable
`ifdef SCR1_CLKCTRL_EN
    input   logic                                           clk_pipe_en,    // Pipeline clock enable
`endif // SCR1_CLKCTRL_EN
    // Control/status registers i/f
    input  logic                                            csr_req,        // CSR i/f request
    input  type_scr1_csr_cmd_sel_e                          csr_cmd,        // CSR i/f command
    input  logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]         csr_addr,       // CSR i/f address
    input  logic [`SCR1_XLEN-1:0]                           csr_wdata,      // CSR i/f write data
    output type_scr1_csr_resp_e                             csr_resp,       // CSR i/f response
    output logic [`SCR1_XLEN-1:0]                           csr_rdata,      // CSR i/f read data
    // HART Run Control i/f
    input  logic                                            pipe_rst_n_qlfy,// Pipeline reset qualifier
    input  logic                                            dm_cmd_req,     // DM-HART Command request
    input  type_scr1_hdu_dbgstates_e                        dm_cmd,         // DM-HART Command
    output logic                                            dm_cmd_resp,    // DM-HART Command response
    output logic                                            dm_cmd_rcode,   // DM-HART Command return code: 0 - Ok; 1 - Error
    output logic                                            dm_hart_event,  // DM-HART Event: 1 if HART debug state changed
    output type_scr1_hdu_hartstatus_s                       dm_hart_status, // DM-HART Status
    // Program Buffer - HART instruction execution i/f
    output logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]             dm_pbuf_addr,   // Program Buffer address - so far request only for 1 instruction
    input  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]            dm_pbuf_instr,  // Program Buffer instruction
    // HART Abstract Data regs i/f
    output logic                                            dm_dreg_req,    // Abstract Data Register request
    output logic                                            dm_dreg_wr,     // Abstract Data Register write
    output logic [`SCR1_XLEN-1:0]                           dm_dreg_wdata,  // Abstract Data Register write data
    input  logic                                            dm_dreg_resp,   // Abstract Data Register response
    input  logic                                            dm_dreg_fail,   // Abstract Data Register fail
    input  logic [`SCR1_XLEN-1:0]                           dm_dreg_rdata,  // Abstract Data Register read data
    //
`ifdef SCR1_BRKM_EN
    // HDU <-> TDU
    output  logic                                           hart_hwbrk_dsbl,        // Disables BRKM
    input   logic                                           hart_tm_dmode_req,      // Trigger Module requests transition to debug mode
    input   logic                                           hart_brkpt_hw,          // Hardware breakpoint on current instruction
`endif // SCR1_BRKM_EN

    // HART Run Status
    input   logic                                           hart_exu_busy,          // EXU busy
    input   logic                                           hart_instret,           // Instruction retired (with or without exception)
    input   logic                                           hart_init_pc,           // Reset exit
    // HART Halt Status
    input   logic                                           hart_exu_exc_req,       // Exception request
    input   logic                                           hart_brkpt,             // Software Breakpoint (EBREAK)
    // HART Run Control
    output  logic                                           hart_fetch_pbuf,        // Fetch instruction from Program Buffer
    output  logic                                           hart_exu_no_commit,     // Forbid instruction commitment
    output  logic                                           hart_exu_irq_dsbl,      // Disable IRQ
    output  logic                                           hart_exu_pc_advmt_dsbl, // Forbid PC advancement
    output  logic                                           hart_exu_dmode_sstep_en,// Enable single-step

    // HART state
    output  logic                                           hart_dbg_halted,        // Debug halted state
    output  logic                                           hart_dbg_run2halt,      // Transition to debug halted state
    output  logic                                           hart_dbg_halt2run,      // Transition to run state
    output  logic                                           hart_dbg_run_start,     // First cycle of run state
`ifndef SCR1_BRKM_EN
    output logic                                            hart_cmd_rctl,
`endif // SCR1_BRKM_EN
    input  logic [`SCR1_XLEN-1:0]                           hart_pc,                // Current PC
    output logic [`SCR1_XLEN-1:0]                           hart_new_pc,            // New PC for resume
    //
    input   logic                                           hart_pbuf_instr_rdy,    // Program Buffer Instruction i/f ready
    output  logic                                           hart_pbuf_instr_vd,     // Program Buffer Instruction valid
    output  logic                                           hart_pbuf_instr_err,    // Program Buffer Instruction i/f error
    output  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]           hart_pbuf_instr         // Program Buffer Instruction itself
);

//======================================================================================================================
// Local Parameters
//======================================================================================================================
localparam int unsigned SCR1_HDU_TIMEOUT           = 64;       // must be power of 2
localparam int unsigned SCR1_HDU_TIMEOUT_WIDTH     = $clog2(SCR1_HDU_TIMEOUT);

//======================================================================================================================
// Local Types
//======================================================================================================================


//======================================================================================================================
// Local Signals
//======================================================================================================================
// -- Debug FSM ----------------------------------------------------------------
type_scr1_hdu_dbgstates_e                           dbg_state;
type_scr1_hdu_dbgstates_e                           dbg_state_next;
logic                                               dfsm_trans;
logic                                               dfsm_trans_next;
logic                                               dfsm_update;
logic                                               dfsm_update_next;
logic                                               dfsm_event;
logic                                               dfsm_event_next;
logic                                               dfsm_csr_update;
logic                                               dfsm_cmd_req;
logic                                               dfsm_pbuf_start_fetch;

logic                                               dfsm_rctl_wr;
logic                                               dfsm_rctl_clr;

// -- HART Status --------------------------------------------------------------
type_scr1_hdu_haltstatus_s                          hart_haltstatus;
type_scr1_hdu_haltcause_e                           hart_haltcause;

// -- HART Run Control ---------------------------------------------------------
logic                                               hart_halt_req;
logic                                               hart_halt_ack;
logic                                               hart_resume_req;
logic                                               hart_cmd_rcode;
`ifdef SCR1_BRKM_EN
logic                                               hart_cmd_rctl;
`endif // SCR1_BRKM_EN
type_scr1_hdu_runctrl_s                             hart_runctrl;
logic                                               dmode_cause_sstep;
logic                                               dmode_cause_except;
logic                                               dmode_cause_ebreak;
`ifdef SCR1_BRKM_EN
logic                                               dmode_cause_tmreq;
`endif // SCR1_BRKM_EN

logic [SCR1_HDU_TIMEOUT_WIDTH-1:0]                  dbgc_timeout_cnt;
logic                                               dbgc_timeout_flag;

// -- PBUF ---------------------------------------------------------------------
type_scr1_hdu_pbufstates_e                          pbuf_state;
type_scr1_hdu_pbufstates_e                          pbuf_state_next;
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]                pbuf_addr;
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]                pbuf_addr_next;
logic                                               pbuf_instr_wait_latching;

// -- Run Control --------------------------------------------------------------


// -- Debug CSRs ---------------------------------------------------------------
// CSRs :: common
logic                                               csr_wr;
logic [`SCR1_XLEN-1:0]                              csr_wr_data;
logic [`SCR1_XLEN-1:0]                              csr_rd_data;
// CSRs :: DCSR
logic                                               csr_dcsr_sel;
logic                                               csr_dcsr_wr;
type_scr1_hdu_dcsr_s                                csr_dcsr_in;
type_scr1_hdu_dcsr_s                                csr_dcsr_out;
logic                                               csr_dcsr_ebreakm;
logic                                               csr_dcsr_stepie;
logic                                               csr_dcsr_step;

logic [SCR1_HDU_DCSR_CAUSE_BIT_L-
       SCR1_HDU_DCSR_CAUSE_BIT_R:0]                 csr_dcsr_cause;

// CSRs :: DPC
logic                                               csr_dpc_sel;
logic                                               csr_dpc_wr;
logic [`SCR1_XLEN-1:0]                              csr_dpc_reg;
logic [`SCR1_XLEN-1:0]                              csr_dpc_in;
logic [`SCR1_XLEN-1:0]                              csr_dpc_out;
// CSRs :: DSCRATCH0
logic                                               csr_dscratch0_sel;
logic                                               csr_dscratch0_wr;
logic [`SCR1_XLEN-1:0]                              csr_dscratch0_out;
type_scr1_csr_resp_e                                csr_dscratch0_resp;
// CSRs :: DSCRATCH1
//logic                                             csr_dscratch1_sel;
//logic                                             csr_dscratch1_wr;
//logic [`SCR1_XLEN-1:0]                            csr_dscratch1_reg;
//logic [`SCR1_XLEN-1:0]                            csr_dscratch1_in;
//logic [`SCR1_XLEN-1:0]                            csr_dscratch1_out;

//======================================================================================================================
// Logic
//======================================================================================================================

// -----------------------------------------------------------------------------
// Debug FSM (Run Control)
// -----------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk)
begin
    if (~rst_n) begin
        dbg_state           <= SCR1_HDU_DBGSTATE_RESET;
        dfsm_trans          <= 1'b0;
        dfsm_update         <= 1'b0;
        dfsm_event          <= 1'b0;
    end
    else begin
        dbg_state           <= dbg_state_next;
        dfsm_trans          <= dfsm_trans_next;
        dfsm_update         <= dfsm_update_next;
        dfsm_event          <= dfsm_event_next;
    end
end

always_comb
begin
    dbg_state_next          = dbg_state;
    dfsm_trans_next         = dfsm_trans;
    dfsm_update_next        = dfsm_update;
    dfsm_event_next         = 1'b0;
    dfsm_csr_update         = 1'b0;
    dfsm_cmd_req            = 1'b0;

    dfsm_rctl_wr            = 1'b0;    
    dfsm_rctl_clr           = 1'b0;
    dfsm_pbuf_start_fetch   = 1'b0;
    dm_cmd_resp             = 1'b0;
    dm_cmd_rcode            = 1'b1;
    hart_dbg_halted         = 1'b0;
    hart_dbg_run_start      = 1'b0;

    case (dbg_state)
        SCR1_HDU_DBGSTATE_RESET: begin
            dfsm_trans_next     = 1'b0;
            dfsm_update_next    = 1'b0;

            if (~pipe_rst_n_qlfy) begin
                hart_dbg_halted     = 1'b1; // Prevent instruction issuing
            end
            else begin
                dfsm_cmd_req        = dm_cmd_req;
                if (hart_init_pc) begin
                    if (dm_cmd_req) begin
                        dm_cmd_resp     = 1'b1;
                        dm_cmd_rcode    = 1'b0;
                        case (dm_cmd)
                            SCR1_HDU_DBGSTATE_DHALTED : begin
                                dbg_state_next  = SCR1_HDU_DBGSTATE_DHALTED;
                                dfsm_csr_update = 1'b1;
                            end
                            default : begin
                                dbg_state_next  = SCR1_HDU_DBGSTATE_RUN;
                            end
                        endcase
                    end
                    else begin
                        dbg_state_next  = SCR1_HDU_DBGSTATE_RUN;
                        dfsm_event_next = 1'b1;
                    end
                end
            end
        end

        SCR1_HDU_DBGSTATE_RUN: begin
            if (~pipe_rst_n_qlfy) begin
                //! hart_dbg_halted     = 1'b1; // Prevent instruction issuing
                dfsm_trans_next     = 1'b0;
                dfsm_update_next    = 1'b0;
                dbg_state_next      = SCR1_HDU_DBGSTATE_RESET;
                dfsm_event_next     = 1'b1;
            end
            else begin
                if (dfsm_update) begin
                    hart_dbg_halted     = 1'b1;
                    dbg_state_next      = SCR1_HDU_DBGSTATE_DHALTED;
                    dfsm_event_next     = 1'b1;
                    dfsm_update_next    = 1'b0;
                    dfsm_csr_update     = 1'b1;
                    dfsm_rctl_clr       = 1'b1;
                    dm_cmd_resp         = dm_cmd_req;
                    dm_cmd_rcode        = 1'b0;//!  Take into account Halt Time-Out!!
                end
                else begin
                    if (dfsm_trans) begin
                        dfsm_cmd_req    = 1'b1;
                        if (hart_halt_ack) begin
                            dfsm_trans_next = 1'b0;
                            dfsm_update_next = 1'b1;
                        end
                    end
                    else begin
                        if (hart_halt_ack) begin
                            dfsm_update_next    = 1'b1;
                        end
                        else begin
                            if (dm_cmd_req & (dm_cmd == SCR1_HDU_DBGSTATE_DHALTED)) begin
                                dfsm_trans_next = 1'b1;
                            end
                        end
                    end
                end
            end
        end

        SCR1_HDU_DBGSTATE_DHALTED: begin
            if (~pipe_rst_n_qlfy) begin
                hart_dbg_halted     = 1'b1; // Prevent instruction issuing
                dfsm_trans_next     = 1'b0;
                dfsm_update_next    = 1'b0;
                dm_cmd_resp         = dm_cmd_req;   // Unexpected reset terminates CMD with error
                dm_cmd_rcode        = 1'b1;
                dbg_state_next      = SCR1_HDU_DBGSTATE_RESET;
                dfsm_event_next     = 1'b1;
            end
            else begin
                if (dfsm_update) begin
                    dfsm_cmd_req            = 1'b1;
                    hart_dbg_halted         = 1'b0;
                    hart_dbg_run_start      = 1'b1;
                    dfsm_update_next        = 1'b0;
                    dm_cmd_resp             = 1'b1;
                    dm_cmd_rcode            = 1'b0;
                    dfsm_pbuf_start_fetch   = hart_cmd_rctl;
                    dbg_state_next          = hart_cmd_rctl ? SCR1_HDU_DBGSTATE_DRUN : SCR1_HDU_DBGSTATE_RUN;
                    dfsm_event_next         = 1'b1;
                end
                else begin
                    hart_dbg_halted         = 1'b1;
                    if (dfsm_trans) begin
                        dfsm_cmd_req        = 1'b1;
                        dfsm_trans_next     = 1'b0;
                        dfsm_update_next    = 1'b1;
                    end
                    else begin
                        hart_dbg_halted     = 1'b1;
                        if (  dm_cmd_req &
                            ((dm_cmd == SCR1_HDU_DBGSTATE_RUN) |
                             (dm_cmd == SCR1_HDU_DBGSTATE_DRUN))
                        ) begin
                            dfsm_trans_next = 1'b1;
                            dfsm_rctl_wr    = 1'b1;
                        end
                    end
                end
            end
        end

        SCR1_HDU_DBGSTATE_DRUN: begin
            if (~pipe_rst_n_qlfy) begin
                hart_dbg_halted     = 1'b1; // Prevent instruction issuing
                dfsm_trans_next     = 1'b0;
                dfsm_update_next    = 1'b0;
                dm_cmd_resp         = dm_cmd_req;   // Unexpected reset terminates CMD with error
                dm_cmd_rcode        = 1'b1;
                dbg_state_next      = SCR1_HDU_DBGSTATE_RESET;
                dfsm_event_next     = 1'b1;
            end
            else begin
                if (dfsm_update) begin
                    hart_dbg_halted     = 1'b1;
                    dbg_state_next      = SCR1_HDU_DBGSTATE_DHALTED;
                    dfsm_event_next     = 1'b1;
                    dfsm_update_next    = 1'b0;
                    dfsm_rctl_clr       = 1'b1;
                    dm_cmd_resp         = dm_cmd_req;
                    dm_cmd_rcode        = 1'b0;//!  Take into account Halt Time-Out!!
                end
                else begin
                    if (dfsm_trans) begin
                        dfsm_cmd_req    = 1'b1;
                        if (hart_halt_ack) begin
                            dfsm_trans_next = 1'b0;
                            dfsm_update_next = 1'b1;
                        end
                    end
                    else begin
                        if (hart_halt_ack) begin
                            dfsm_update_next    = 1'b1;
                        end
                        else begin
                            if (dm_cmd_req & (dm_cmd == SCR1_HDU_DBGSTATE_DHALTED)) begin
                                dfsm_trans_next = 1'b1;
                            end
                        end
                    end
                end
            end
        end

        default: begin
            dbg_state_next = SCR1_HDU_DBGSTATE_XXX;
        end
    endcase
end

always_comb
begin
    dm_hart_status              = '0;
    dm_hart_status.dbg_state    = dbg_state;
    dm_hart_status.except       = (dbg_state == SCR1_HDU_DBGSTATE_DHALTED) ? hart_haltstatus.except : 1'b0;
    dm_hart_status.ebreak       = (dbg_state == SCR1_HDU_DBGSTATE_DHALTED) ?
                                    ((hart_haltstatus.cause == SCR1_HDU_HALTCAUSE_EBREAK) ? 1'b1 : 1'b0)
                                    : 1'b0;
end
assign dm_hart_event = dfsm_event;

// -----------------------------------------------------------------------------
// HART Run Status
// -----------------------------------------------------------------------------

// Debug mode entry cause
assign dmode_cause_sstep    = hart_runctrl.redirect.sstep & hart_instret;
assign dmode_cause_except   = (dbg_state == SCR1_HDU_DBGSTATE_DRUN) & hart_exu_exc_req
`ifdef SCR1_BRKM_EN
                                & (~hart_brkpt_hw)
`endif // SCR1_BRKM_EN
                                & (~hart_brkpt);
assign dmode_cause_ebreak   = hart_runctrl.redirect.ebreak & hart_brkpt;
`ifdef SCR1_BRKM_EN
assign dmode_cause_tmreq    = hart_tm_dmode_req & hart_brkpt_hw;
`endif // SCR1_BRKM_EN

// State transition control
assign hart_dbg_run2halt    = ~hart_dbg_halted & (
    dbgc_timeout_flag | (
        ~hart_exu_busy & (
            dmode_cause_sstep |
            dmode_cause_ebreak |
            dmode_cause_except |
            hart_halt_req
`ifdef SCR1_BRKM_EN
            | dmode_cause_tmreq
`endif // SCR1_BRKM_EN
            )
        )
    )
`ifdef SCR1_CLKCTRL_EN
    & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
    ;

assign hart_dbg_halt2run    = hart_dbg_halted & hart_resume_req
`ifdef SCR1_CLKCTRL_EN
                                & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
    ;
assign hart_halt_ack = hart_dbg_run2halt;

// -----------------------------------------------------------------------------
// HART Run Control
// -----------------------------------------------------------------------------

always_comb
begin
    hart_halt_req   = 1'b0;
    hart_resume_req = 1'b0;
    hart_cmd_rctl   = 1'b0;

    case (dm_cmd)
        SCR1_HDU_DBGSTATE_RUN : begin
            hart_resume_req = dfsm_cmd_req;
        end
        SCR1_HDU_DBGSTATE_DRUN : begin
            hart_resume_req = dfsm_cmd_req;
            hart_cmd_rctl   = 1'b1;
        end
        SCR1_HDU_DBGSTATE_DHALTED : begin
            hart_halt_req   = dfsm_cmd_req;
        end
        default : begin
        end
    endcase
end

always_ff @(negedge rst_n, posedge clk)
begin
    if (~rst_n) begin
        hart_runctrl.irq_dsbl                   <= 1'b0;
        hart_runctrl.fetch_src                  <= SCR1_HDU_FETCH_SRC_NORMAL;
        hart_runctrl.pc_advmt_dsbl              <= 1'b0;
        hart_runctrl.hwbrkpt_dsbl               <= 1'b0;
        hart_runctrl.redirect                   <= '0;
    end
    else if(clk_en) begin
        if (dfsm_rctl_clr) begin
            hart_runctrl                                    <= '0;
        end
        else begin
            if (dfsm_rctl_wr) begin
                if (~hart_cmd_rctl) begin
                    // Case : resume to RUN state
                    hart_runctrl.irq_dsbl                   <= csr_dcsr_step ? ~csr_dcsr_stepie : 1'b0;
                    hart_runctrl.fetch_src                  <= SCR1_HDU_FETCH_SRC_NORMAL;
                    hart_runctrl.pc_advmt_dsbl              <= 1'b0;
                    hart_runctrl.hwbrkpt_dsbl               <= 1'b0;
                    hart_runctrl.redirect.sstep             <= csr_dcsr_step;
                    hart_runctrl.redirect.ebreak            <= csr_dcsr_ebreakm;
                end
                else begin
                    // Case : resume to DRUN state
                    hart_runctrl.irq_dsbl                   <= 1'b1;
                    hart_runctrl.fetch_src                  <= SCR1_HDU_FETCH_SRC_PBUF;
                    hart_runctrl.pc_advmt_dsbl              <= 1'b1;
                    hart_runctrl.hwbrkpt_dsbl               <= 1'b1;
                    hart_runctrl.redirect.sstep             <= 1'b0;
                    hart_runctrl.redirect.ebreak            <= 1'b1;
                end
            end
        end
    end
end

assign hart_fetch_pbuf          = hart_runctrl.fetch_src;
assign hart_exu_irq_dsbl        = hart_runctrl.irq_dsbl;
assign hart_exu_pc_advmt_dsbl   = hart_runctrl.pc_advmt_dsbl;
`ifdef SCR1_BRKM_EN
assign hart_hwbrk_dsbl          = hart_runctrl.hwbrkpt_dsbl;
`endif // SCR1_BRKM_EN
// No change in arch. state if dmode caused by breakpoint
assign hart_exu_no_commit       = dmode_cause_ebreak
`ifdef SCR1_BRKM_EN
                                | dmode_cause_tmreq
`endif // SCR1_BRKM_EN
    ;
assign hart_exu_dmode_sstep_en  = hart_runctrl.redirect.sstep;

// -----------------------------------------------------------------------------
// HART Halt Status
// -----------------------------------------------------------------------------
always_comb
begin
    case (1'b1)
`ifdef SCR1_BRKM_EN
        // Trigger Module request has the highest priority
        dmode_cause_tmreq   : hart_haltcause = SCR1_HDU_HALTCAUSE_TMREQ;
`endif // SCR1_BRKM_EN
        dmode_cause_ebreak  : hart_haltcause = SCR1_HDU_HALTCAUSE_EBREAK;
        hart_halt_req       : hart_haltcause = SCR1_HDU_HALTCAUSE_DMREQ;
        dmode_cause_sstep   : hart_haltcause = SCR1_HDU_HALTCAUSE_SSTEP;
        default             : hart_haltcause = SCR1_HDU_HALTCAUSE_NONE;
    endcase
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        hart_haltstatus                  <= '0;
    end else begin
        if (hart_halt_ack) begin
            hart_haltstatus.except       <= dmode_cause_except;
            // Debug mode entry cause
            hart_haltstatus.cause        <= hart_haltcause;
        end
    end
end

// -----------------------------------------------------------------------------
// Halt Request Time-Out
// -----------------------------------------------------------------------------
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dbgc_timeout_cnt <= '1;
    end else begin
        if (hart_dbg_halt2run) begin
            dbgc_timeout_cnt <= '1;
        end
        else if (hart_halt_req & ~hart_dbg_run2halt) begin
            dbgc_timeout_cnt <= dbgc_timeout_cnt - 1'b1;
        end
    end
end
assign dbgc_timeout_flag = ~|dbgc_timeout_cnt;

// -----------------------------------------------------------------------------
// Program Buffer (PBUF)
// -----------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk)
begin
    if (~rst_n) begin
        pbuf_state <= SCR1_HDU_PBUFSTATE_IDLE;
        pbuf_addr  <= '0;
    end
    else if(clk_en) begin
        pbuf_state <= pbuf_state_next;
        pbuf_addr  <= pbuf_addr_next;
    end
end
assign dm_pbuf_addr = pbuf_addr;

always_comb
begin
    pbuf_state_next         = pbuf_state;
    pbuf_addr_next          = pbuf_addr;
    hart_pbuf_instr_vd      = 1'b0;
    hart_pbuf_instr_err     = 1'b0;

    case (pbuf_state)

        SCR1_HDU_PBUFSTATE_IDLE: begin
            pbuf_addr_next = '0;
            if (dfsm_pbuf_start_fetch) begin
                pbuf_state_next = SCR1_HDU_PBUFSTATE_FETCH;
            end
        end

        SCR1_HDU_PBUFSTATE_FETCH: begin
            hart_pbuf_instr_vd      = ~pbuf_instr_wait_latching;
            if (hart_exu_exc_req) begin
                pbuf_state_next     = SCR1_HDU_PBUFSTATE_WAIT4END;
            end
            else begin
                if (hart_pbuf_instr_vd & hart_pbuf_instr_rdy) begin
                    if (pbuf_addr == (SCR1_HDU_PBUF_ADDR_SPAN-1)) begin
                        pbuf_state_next = SCR1_HDU_PBUFSTATE_EXCINJECT;
                    end
                    else begin
                        pbuf_addr_next = pbuf_addr + 1'b1;
                    end
                end
            end
        end

        SCR1_HDU_PBUFSTATE_EXCINJECT: begin
            hart_pbuf_instr_vd      = ~pbuf_instr_wait_latching;
            hart_pbuf_instr_err     = 1'b1;
            if (hart_exu_exc_req) begin
                pbuf_state_next     = SCR1_HDU_PBUFSTATE_WAIT4END;
            end
            else begin
                if (hart_pbuf_instr_vd & hart_pbuf_instr_rdy) begin
                    pbuf_state_next = SCR1_HDU_PBUFSTATE_WAIT4END;
                end
            end
        end

        SCR1_HDU_PBUFSTATE_WAIT4END: begin
            if (hart_dbg_halted) begin
                pbuf_state_next = SCR1_HDU_PBUFSTATE_IDLE;
            end
        end

        default: begin
        end
    endcase
end

// Pass instruction from debug program buffer to cpu pipeline with two options:
// - through register, better for frequency
// - through wires, better for area
generate if( HART_PBUF_INSTR_REGOUT_EN == 1'b1  ) begin // Pass trhough register
    always @(posedge clk, negedge rst_n) begin
        if( ~rst_n ) pbuf_instr_wait_latching <= 1'b0;
        else         pbuf_instr_wait_latching <= hart_pbuf_instr_vd & hart_pbuf_instr_rdy;
    end

    always @(posedge clk) begin
        hart_pbuf_instr <= dm_pbuf_instr;
    end
end else begin // Pass trhough wires
    assign pbuf_instr_wait_latching = 1'b0;
    assign hart_pbuf_instr          = dm_pbuf_instr;
end endgenerate

// -----------------------------------------------------------------------------
// CSRs :: Interface
// -----------------------------------------------------------------------------

// CSRs :: Interface :: Reg Select
always_comb
begin : csr_if_regsel
    csr_dcsr_sel        = 1'b0;
    csr_dpc_sel         = 1'b0;
    csr_dscratch0_sel   = 1'b0;
    //csr_dscratch1_sel   = 1'b0;

    if (csr_req == 1'b1) begin
        case (csr_addr)
            SCR1_HDU_DBGCSR_OFFS_DCSR : begin
                csr_dcsr_sel        = 1'b1;
            end

            SCR1_HDU_DBGCSR_OFFS_DPC : begin
                csr_dpc_sel         = 1'b1;
            end

            SCR1_HDU_DBGCSR_OFFS_DSCRATCH0 : begin
                csr_dscratch0_sel   = 1'b1;
            end

            //SCR1_HDU_DBGCSR_OFFS_DSCRATCH1 : begin
            //    csr_dscratch1_sel   = 1'b1;
            //end

            default : begin
                csr_dcsr_sel        = 1'bX;
                csr_dpc_sel         = 1'bX;
                csr_dscratch0_sel   = 1'bX;
                //csr_dscratch1_sel   = 1'bX;
            end
        endcase
    end
end : csr_if_regsel

// CSRs :: Interface :: Read Data
always_comb
begin : csr_if_rddata

    csr_rd_data =   csr_dcsr_out      |
                    csr_dpc_out       |
//                    csr_dscratch1_out |
                    csr_dscratch0_out;
end : csr_if_rddata

// CSRs :: Interface :: Writing
always_comb
begin : csr_if_write
    csr_wr          = 1'b0;
    csr_wr_data     = '0;

    if (csr_req == 1'b1) begin
        case (csr_cmd)
            SCR1_CSR_CMD_WRITE : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr_wdata;
            end

            SCR1_CSR_CMD_SET : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr_rd_data | ( csr_wdata);
            end

            SCR1_CSR_CMD_CLEAR : begin
                csr_wr          = 1'b1;
                csr_wr_data     = csr_rd_data & (~csr_wdata);
            end

            default : begin
                csr_wr_data     = 'X;
            end
        endcase
    end
end : csr_if_write

// CSRs :: Interface :: Response
always_comb
begin
    if (dbg_state == SCR1_HDU_DBGSTATE_DRUN) begin
        case (csr_addr)
                SCR1_HDU_DBGCSR_OFFS_DSCRATCH0 : begin
                    csr_resp = csr_dscratch0_resp;
                end

                default : begin
                    csr_resp = (csr_req == 1'b1) ?
                                SCR1_CSR_RESP_OK :
                                SCR1_CSR_RESP_ER;
                end
        endcase
    end
    else begin
        csr_resp = SCR1_CSR_RESP_ER;
    end
end
assign csr_rdata   = csr_rd_data;

// -----------------------------------------------------------------------------
// CSRs :: DCSR
// -----------------------------------------------------------------------------
always_comb
begin
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

always_ff @(negedge rst_n, posedge clk)
begin
    if (rst_n == 1'b0) begin
        csr_dcsr_ebreakm        <= 1'b0;
        csr_dcsr_stepie         <= 1'b0;
        csr_dcsr_step           <= 1'b0;
    end
    else if(clk_en) begin
        if (csr_dcsr_wr) begin
            csr_dcsr_ebreakm    <= csr_dcsr_in.ebreakm;
            csr_dcsr_stepie     <= csr_dcsr_in.stepie;
            csr_dcsr_step       <= csr_dcsr_in.step;
        end
    end
end

always_ff @(negedge rst_n, posedge clk)
begin
    if (rst_n == 1'b0) begin
        csr_dcsr_cause <= 1'b0;
    end
    else if(clk_en) begin
        if(dfsm_csr_update) begin
            csr_dcsr_cause <= hart_haltstatus.cause;
        end
    end
end


// -----------------------------------------------------------------------------
// CSRs :: DPC
// -----------------------------------------------------------------------------
always_comb
begin
    csr_dpc_in                 = csr_wr_data;
    csr_dpc_wr                 = csr_wr & csr_dpc_sel;

    csr_dpc_out                = csr_dpc_sel ? csr_dpc_reg : '0;
end

always_ff @(negedge rst_n, posedge clk)
begin
    if (rst_n == 1'b0) begin
        csr_dpc_reg        <= '0;
    end
    else if(clk_en) begin
        if (dfsm_csr_update) begin
            csr_dpc_reg    <= hart_pc;
        end
        else if (csr_dpc_wr) begin
            csr_dpc_reg    <= csr_dpc_in;
        end
    end
end
assign hart_new_pc = csr_dpc_reg;

// -----------------------------------------------------------------------------
// CSRs :: DSCRATCH0
// -----------------------------------------------------------------------------
always_comb
begin
    dm_dreg_req         = csr_dscratch0_sel;
    dm_dreg_wr          = csr_wr & csr_dscratch0_sel;
    dm_dreg_wdata       = csr_wr_data;
    csr_dscratch0_out   = csr_dscratch0_sel ? dm_dreg_rdata : '0;

    csr_dscratch0_resp  = dm_dreg_resp ?
                            (dm_dreg_fail ? SCR1_CSR_RESP_ER : SCR1_CSR_RESP_OK) :
                            SCR1_CSR_RESP_ER;
end

`ifdef SCR1_SIM_ENV
`ifndef VERILATOR
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SVA_HDU_XCHECK_COMMON :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {rst_n,clk,clk_en,csr_req,pipe_rst_n_qlfy} )
    )
    else $error("HDU Error: common signals are in X state");

SVA_HDU_XCHECK_CSR_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        csr_req |-> !$isunknown( {csr_cmd,csr_addr,csr_wdata} )
    )
    else $error("HDU Error: CSR i/f is in X state");

SVA_HDU_XCHECK_DM_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {dm_cmd_req,dm_cmd,dm_dreg_resp,
        dm_dreg_fail} )
    )
    else $error("HDU Error: DM i/f is in X state");

SVA_HDU_XCHECK_TDU_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {hart_tm_dmode_req,hart_brkpt_hw} )
    )
    else $error("HDU Error: TDU i/f is in X state");

SVA_HDU_XCHECK_HART_INTF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {hart_exu_busy,hart_instret,hart_init_pc,hart_exu_exc_req,hart_brkpt,
        hart_pc,hart_pbuf_instr_rdy} )
    )
    else $error("HDU Error: HART i/f is in X state");

`endif // VERILATOR
`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_hdu

`endif // SCR1_DBGC_EN
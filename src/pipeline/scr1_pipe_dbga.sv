/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_dbga.sv>
/// @brief      Debug Agent (DBGA)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_dbgc.svh"

module scr1_pipe_dbga (
    // Common
    input   logic                                           rst_n,
    input   logic                                           clk,
`ifdef SCR1_CLKCTRL_EN
    input   logic                                           clk_pipe_en,
`endif // SCR1_CLKCTRL_EN

    // DBGA <-> DBGC
    input   type_scr1_dbgc_hart_dbg_mode_e                  dbgc_hart_cmd,          // 1 - debug halt, 0 - run
    input   logic                                           dbgc_hart_cmd_req,
    output  logic                                           dbgc_hart_cmd_ack,
    output  logic                                           dbgc_hart_cmd_nack,
    input   type_scr1_dbgc_hart_runctrl_s                   dbgc_hart_runctrl,      // core run control (set by DBGC)
    output  type_scr1_dbgc_hart_state_s                     dbgc_hart_state,        // core state (set by core)
    input   logic [SCR1_DBGC_DBG_CORE_INSTR_WIDTH-1:0]      dbgc_hart_instr,        // instruction from DBGC to core
    input   logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbgc_hart_dreg_out,     // DDR DBGC->CORE
    output  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbgc_hart_dreg_in,      // DDR CORE->DBGC
    output  logic                                           dbgc_hart_dreg_wr,      // 1 - write to DDR (from core)

    // DBGA <-> IFU
    output  logic                                           fetch_dbgc,             // Fetch instructions provided by DBGC
    output  logic [`SCR1_IMEM_DWIDTH-1:0]                   dbgc_instr,

`ifdef SCR1_BRKM_EN
    // DBGA <-> BRKM
    output  logic                                           hwbrk_dsbl,             // Disables BRKM
    input   logic                                           brkm_dmode_req,         // BRKM requests transition to debug mode
    input   logic                                           brkpt_hw,               // Hardware breakpoint on current instruction
`endif // SCR1_BRKM_EN

    // DBGA <-> EXU
    input   logic                                           exu_busy,               // EXU busy
    input   logic                                           instret,                // Instruction retired (with or without exception)
    input   logic                                           exu_exc_req,            // Exception request
    input   logic                                           brkpt,                  // Breakpoint (sw/hw) on current instruction
    input   logic                                           exu_init_pc,            // Reset exit
    output  logic                                           exu_no_commit,          // Forbid instruction commitment
    output  logic                                           exu_irq_dsbl,           // Disable IRQ
    output  logic                                           exu_pc_advmt_dsbl,      // Forbid PC advancement
    output  logic                                           exu_dmode_sstep_en,     // Enable single-step

    // DBGA <-> CSR
    output  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbga2csr_ddr,           // DBGA read data
    input   logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        csr2dbga_ddr,           // DBGA write data
    input   logic                                           csr2dbga_ddr_we,        // DBGA write request

    // Core state
    output  logic                                           dbg_halted,             // Debug halted state
    output  logic                                           dbg_run2halt,           // Transition to debug halted state
    output  logic                                           dbg_halt2run,           // Transition to run state
    output  logic                                           dbg_run_start           // First cycle of run state
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------
localparam SCR1_DBGC_TIMEOUT        = 64;       // must be power of 2
localparam SCR1_DBGC_TIMEOUT_WIDTH  = $clog2(SCR1_DBGC_TIMEOUT);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic                               dmode_cause_rst;
logic                               dmode_cause_sstep;
logic                               dmode_cause_brk;
`ifdef SCR1_BRKM_EN
logic                               dmode_cause_brkm_req;
`endif // SCR1_BRKM_EN

logic                               enforce_dbg_mode;
logic                               enforce_run_mode;

logic [SCR1_DBGC_TIMEOUT_WIDTH-1:0] dbgc_timeout_cnt;
logic                               dbgc_timeout_flag;

//-------------------------------------------------------------------------------
// Core state
//-------------------------------------------------------------------------------

// Debug mode entry cause
assign dmode_cause_rst      = dbgc_hart_runctrl.dmode_en.rst_brk & exu_init_pc;
assign dmode_cause_sstep    = dbgc_hart_runctrl.dmode_en.sstep & instret;
assign dmode_cause_brk      = dbgc_hart_runctrl.dmode_en.brkpt & brkpt;
`ifdef SCR1_BRKM_EN
assign dmode_cause_brkm_req = brkm_dmode_req & brkpt_hw;
`endif // SCR1_BRKM_EN

// Enforce conditions
assign enforce_dbg_mode     = dbgc_hart_cmd_req & (dbgc_hart_cmd == SCR1_DBGC_HART_DBG_MODE);
assign enforce_run_mode     = dbgc_hart_cmd_req & (dbgc_hart_cmd == SCR1_DBGC_HART_RUN_MODE);

assign dbg_run2halt         = ~dbg_halted & (
    dbgc_timeout_flag | (
        ~exu_busy & (
            dmode_cause_rst | dmode_cause_sstep | dmode_cause_brk | enforce_dbg_mode
`ifdef SCR1_BRKM_EN
            | dmode_cause_brkm_req
`endif // SCR1_BRKM_EN
            )
        )
    )
`ifdef SCR1_CLKCTRL_EN
    & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
    ;

assign dbg_halt2run         = dbg_halted & enforce_run_mode
`ifdef SCR1_CLKCTRL_EN
                                & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                                ;

assign dbgc_hart_cmd_ack    = (dbg_halt2run | (~dbg_halted & enforce_dbg_mode & ~exu_busy))
`ifdef SCR1_CLKCTRL_EN
                                & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                                ;

assign dbgc_hart_cmd_nack   = ((dbg_halted & enforce_dbg_mode) |
                              (~dbg_halted & enforce_run_mode) |
                              (~dbg_halted & enforce_dbg_mode & dbgc_timeout_flag))
`ifdef SCR1_CLKCTRL_EN
                                & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                                ;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dbg_halted      <= 1'b0;
    end else begin
        if (dbg_run2halt) begin
            dbg_halted  <= 1'b1;
        end else
        if (dbg_halt2run) begin
            dbg_halted  <= 1'b0;
        end
    end
end

always_ff @(posedge clk) begin
    dbg_run_start   <= dbg_halt2run;
end


// Timeout
assign dbgc_timeout_flag = ~|dbgc_timeout_cnt;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dbgc_timeout_cnt <= '1;
    end else begin
        if (dbg_halt2run) begin
            dbgc_timeout_cnt <= '1;
        end
        else if (enforce_dbg_mode & ~dbg_run2halt) begin
            dbgc_timeout_cnt <= dbgc_timeout_cnt - 1'b1;
        end
    end
end


//-------------------------------------------------------------------------------
// Hart RUNCTRL struct & various run stuff
//-------------------------------------------------------------------------------

assign exu_irq_dsbl             = (dbgc_hart_runctrl.irq_dsbl == SCR1_DBGC_HART_IRQ_DSBL_ACTIVE);
assign exu_pc_advmt_dsbl        = dbgc_hart_runctrl.pc_advmt_dsbl;
`ifdef SCR1_BRKM_EN
assign hwbrk_dsbl               = dbgc_hart_runctrl.brkpt_hw_dsbl;
`endif // SCR1_BRKM_EN

// No change in arch. state if dmode caused by breakpoint
assign exu_no_commit            = dmode_cause_brk
`ifdef SCR1_BRKM_EN
                                | dmode_cause_brkm_req
`endif // SCR1_BRKM_EN
;
assign exu_dmode_sstep_en       = dbgc_hart_runctrl.dmode_en.sstep;

assign dbgc_instr               = dbgc_hart_instr;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        fetch_dbgc  <= 1'b0;
    end else begin
        if (dbg_halt2run) begin
            fetch_dbgc  <= (dbgc_hart_runctrl.fetch_src == SCR1_DBGC_HART_FETCH_SRC_DBGC);
        end
`ifdef SCR1_EXU_STAGE_BYPASS
        else if (fetch_dbgc & instret) begin
`else // SCR1_EXU_STAGE_BYPASS
        else if (fetch_dbgc) begin
`endif // SCR1_EXU_STAGE_BYPASS
            fetch_dbgc  <= 1'b0;
        end
    end
end


//-------------------------------------------------------------------------------
// Hart STATE struct
//-------------------------------------------------------------------------------

assign dbgc_hart_state.halted   = dbg_halted;
assign dbgc_hart_state.timeout  = dbgc_timeout_flag;
assign dbgc_hart_state.error    = 1'b0;         // unused
assign dbgc_hart_state.commit   = 1'b0;         // unused

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dbgc_hart_state.except                  <= 1'b0;
        dbgc_hart_state.dmode_cause.enforce     <= 1'b0;
        dbgc_hart_state.dmode_cause.rst_brk     <= 1'b0;
        dbgc_hart_state.dmode_cause.sstep       <= 1'b0;
        dbgc_hart_state.dmode_cause.brkpt       <= 1'b0;
        dbgc_hart_state.dmode_cause.brkpt_hw    <= 1'b0;
    end else begin
        if (dbg_run2halt) begin
            dbgc_hart_state.except                  <= exu_exc_req;
            // Debug mode entry cause
            dbgc_hart_state.dmode_cause.enforce     <= enforce_dbg_mode;
            dbgc_hart_state.dmode_cause.rst_brk     <= dmode_cause_rst;
            dbgc_hart_state.dmode_cause.sstep       <= dmode_cause_sstep;
`ifdef SCR1_BRKM_EN
            dbgc_hart_state.dmode_cause.brkpt       <= (dmode_cause_brk | dmode_cause_brkm_req);
            dbgc_hart_state.dmode_cause.brkpt_hw    <= (dmode_cause_brk | dmode_cause_brkm_req) & brkpt_hw;
`else // SCR1_BRKM_EN
            dbgc_hart_state.dmode_cause.brkpt       <= dmode_cause_brk;
            dbgc_hart_state.dmode_cause.brkpt_hw    <= 1'b0;
`endif // SCR1_BRKM_EN
        end // dbg_run2halt
    end
end


//-------------------------------------------------------------------------------
// Debug data register (DDR)
//-------------------------------------------------------------------------------

assign dbga2csr_ddr         = dbgc_hart_dreg_out;
assign dbgc_hart_dreg_in    = csr2dbga_ddr;
assign dbgc_hart_dreg_wr    = csr2dbga_ddr_we;

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SCR1_COV_DBGA_ACK : cover property (
    @(negedge clk) disable iff (~rst_n)
    enforce_dbg_mode & ~dbgc_hart_cmd_ack
);

SCR1_SVA_DBGA_HALT_CHK : assert property (
    @(negedge clk) disable iff (~rst_n)
    dbg_halted |-> ~instret
) else $warning("DBGA warning: instret during dbg_halt");

SCR1_SVA_DBGA_H2R : assert property (
    @(negedge clk) disable iff (~rst_n)
    dbg_halt2run |=> ~dbg_halt2run
) else $error("DBGA Error: more than 1 cycle");

SCR1_SVA_DBGA_R2H : assert property (
    @(negedge clk) disable iff (~rst_n)
    dbg_run2halt |=> ~dbg_run2halt
) else $error("DBGA Error: more than 1 cycle");

SCR1_SVA_DBGA_SSTEP : assert property (
    @(negedge clk) disable iff (~rst_n)
    (dbg_run_start & ~fetch_dbgc) |=> ~dbg_halted
) else $error("DBGA Error: sstep must be at least 2 cycles");

SCR1_SVA_DBGA_HALT : assert property (
    @(negedge clk) disable iff (~rst_n)
    (dbg_run2halt & ~dbgc_timeout_flag) |-> ~exu_busy
) else $error("DBGA Error: core not ready to halt");

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_dbga

`endif // SCR1_DBGC_EN
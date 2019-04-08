/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_pipe_exu.sv>
/// @brief      Execution Unit (EXU)
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_csr.svh"

`ifdef SCR1_DBGC_EN
 `include "scr1_hdu.svh"
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
 `include "scr1_tdu.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_exu (
    // Common
    input   logic                               rst_n,
    input   logic                               clk,
`ifdef SCR1_CLKCTRL_EN
    input   logic                               clk_alw_on,
    input   logic                               clk_pipe_en,
`endif // SCR1_CLKCTRL_EN

    // IDU <-> EXU interface
    input   logic                               idu2exu_req,            // Request form IDU to EXU
    output  logic                               exu2idu_rdy,            // EXU ready for new data from IDU
    input   type_scr1_exu_cmd_s                 idu2exu_cmd,            // EXU command
    input   logic                               idu2exu_use_rs1,        // Clock gating on rs1_addr field
    input   logic                               idu2exu_use_rs2,        // Clock gating on rs2_addr field
`ifndef SCR1_EXU_STAGE_BYPASS
    input   logic                               idu2exu_use_rd,         // Clock gating on rd_addr field
    input   logic                               idu2exu_use_imm,        // Clock gating on imm field
`endif // SCR1_EXU_STAGE_BYPASS

    // EXU <-> MPRF interface
    output  logic [`SCR1_MPRF_ADDR_WIDTH-1:0]   exu2mprf_rs1_addr,      // MPRF rs1 read address
    input   logic [`SCR1_XLEN-1:0]              mprf2exu_rs1_data,      // MPRF rs1 read data
    output  logic [`SCR1_MPRF_ADDR_WIDTH-1:0]   exu2mprf_rs2_addr,      // MPRF rs2 read address
    input   logic [`SCR1_XLEN-1:0]              mprf2exu_rs2_data,      // MPRF rs2 read data
    output  logic                               exu2mprf_w_req,         // MPRF write request
    output  logic [`SCR1_MPRF_ADDR_WIDTH-1:0]   exu2mprf_rd_addr,       // MPRF rd write address
    output  logic [`SCR1_XLEN-1:0]              exu2mprf_rd_data,       // MPRF rd write data

    // EXU <-> CSR read/write interface
    output  logic [SCR1_CSR_ADDR_WIDTH-1:0]     exu2csr_rw_addr,        // CSR read/write address
    output  logic                               exu2csr_r_req,          // CSR read request
    input   logic [`SCR1_XLEN-1:0]              csr2exu_r_data,         // CSR read data
    output  logic                               exu2csr_w_req,          // CSR write request
    output  type_scr1_csr_cmd_sel_e             exu2csr_w_cmd,          // CSR write command
    output  logic [`SCR1_XLEN-1:0]              exu2csr_w_data,         // CSR write data
    input   logic                               csr2exu_rw_exc,         // CSR read/write access exception

    // EXU <-> CSR event interface
    output  logic                               exu2csr_take_irq,       // Take IRQ trap
    output  logic                               exu2csr_take_exc,       // Take exception trap
    output  logic                               exu2csr_mret_update,    // MRET update CSR
    output  logic                               exu2csr_mret_instr,     // MRET instruction
    output  type_scr1_exc_code_e                exu2csr_exc_code,       // Exception code (see scr1_arch_types.svh)
    output  logic [`SCR1_XLEN-1:0]              exu2csr_trap_val,       // Trap value
    input   logic [`SCR1_XLEN-1:0]              csr2exu_new_pc,         // Exception/IRQ/MRET new PC
    input   logic                               csr2exu_irq,            // IRQ request
    input   logic                               csr2exu_ip_ie,          // Some IRQ pending and locally enabled
    input   logic                               csr2exu_mstatus_mie_up, // MSTATUS or MIE update in the current cycle

    // EXU <-> DMEM interface
    output  logic                               exu2dmem_req,           // Data memory request
    output  type_scr1_mem_cmd_e                 exu2dmem_cmd,           // Data memory command
    output  type_scr1_mem_width_e               exu2dmem_width,         // Data memory width
    output  logic [`SCR1_DMEM_AWIDTH-1:0]       exu2dmem_addr,          // Data memory address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]       exu2dmem_wdata,         // Data memory write data
    input   logic                               dmem2exu_req_ack,       // Data memory request acknowledge
    input   logic [`SCR1_DMEM_DWIDTH-1:0]       dmem2exu_rdata,         // Data memory read data
    input   type_scr1_mem_resp_e                dmem2exu_resp,          // Data memory response

    // EXU control
    output  logic                               exu_exc_req,            // Exception on last instruction
    output  logic                               brkpt,                  // Software Breakpoint (EBREAK)
    output  logic                               exu_init_pc,            // Reset exit
    output  logic                               wfi_run2halt,           // Transition to WFI halted state
    output  logic                               instret,                // Instruction retired (with or without exception)
    output  logic                               instret_nexc,           // Instruction retired (without exception)
    output  logic                               exu_busy,               // EXU busy

`ifdef SCR1_DBGC_EN
    // EXU <-> HDU interface
    input   logic                               exu_no_commit,          // Forbid instruction commitment
    input   logic                               exu_irq_dsbl,           // Disable IRQ
    input   logic                               exu_pc_advmt_dsbl,      // Forbid PC advancement
    input   logic                               exu_dmode_sstep_en,     // Enable single-step
    input   logic                               fetch_pbuf,             // Take instructions from Program Buffer
    input   logic                               dbg_halted,             // Debug halted state
    input   logic                               dbg_run2halt,           // Transition to debug halted state
    input   logic                               dbg_halt2run,           // Transition to run state
    input   logic                               dbg_run_start,          // First cycle of run state
    input   logic [`SCR1_XLEN-1:0]              dbg_new_pc,             // New PC as starting point for HART Resume
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
    // EXU <-> TDU interface
    output type_scr1_brkm_instr_mon_s           exu2tdu_i_mon,          // Instruction monitor
    input  logic [SCR1_TDU_ALLTRIG_NUM-1:0]     tdu2exu_i_match,        // Instruction breakpoint(s) match
    input  logic                                tdu2exu_i_x_req,        // Instruction breakpoint exception
    output type_scr1_brkm_lsu_mon_s             lsu2tdu_d_mon,          // Data monitor
    input  logic                                tdu2lsu_i_x_req,        // Instruction breakpoint exception
    input  logic [SCR1_TDU_MTRIG_NUM-1:0]       tdu2lsu_d_match,        // Data breakpoint(s) match
    input  logic                                tdu2lsu_d_x_req,        // Data breakpoint exception
    output logic [SCR1_TDU_ALLTRIG_NUM-1:0]     exu2tdu_bp_retire,      // Instruction with breakpoint flag retire
    output logic                                brkpt_hw,               // Hardware breakpoint on current instruction
`endif // SCR1_BRKM_EN

    // PC interface
`ifdef SCR1_CLKCTRL_EN
    output  logic                               wfi_halted,             // WFI halted state
`endif // SCR1_CLKCTRL_EN
    output  logic [`SCR1_XLEN-1:0]              curr_pc,                // Current PC
    output  logic [`SCR1_XLEN-1:0]              next_pc,                // Next PC
    output  logic                               new_pc_req,             // New PC request
    output  logic [`SCR1_XLEN-1:0]              new_pc                  // New PC data
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------

localparam SCR1_JUMP_MASK = `SCR1_XLEN'hFFFF_FFFE;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Instruction queue
logic                           exu_queue_vd;
type_scr1_exu_cmd_s             exu_queue;
logic                           queue_barrier;

`ifndef SCR1_EXU_STAGE_BYPASS
logic                           idu2exu_use_rs1_r;
logic                           idu2exu_use_rs2_r;
`endif // SCR1_EXU_STAGE_BYPASS

logic                           exu_rdy;

// IALU interface
`ifdef SCR1_RVM_EXT
logic                           ialu_rdy;
logic                           ialu_vd;
`endif // SCR1_RVM_EXT
logic [`SCR1_XLEN-1:0]          ialu_op1;
logic [`SCR1_XLEN-1:0]          ialu_op2;
logic [`SCR1_XLEN-1:0]          ialu_sum2_op1;
logic [`SCR1_XLEN-1:0]          ialu_sum2_op2;
logic [`SCR1_XLEN-1:0]          ialu_res;
logic [`SCR1_XLEN-1:0]          ialu_sum2_res;
logic                           ialu_cmp;

// LSU signals
logic                           lsu_req;
logic                           lsu_rdy;
logic [`SCR1_XLEN-1:0]          lsu_l_data;
logic                           lsu_exc;
type_scr1_exc_code_e            lsu_exc_code;

// CSR signals
enum logic {SCR1_CSR_INIT,
            SCR1_CSR_RDY}       csr_access;

// Exception/Interrupt signals
logic                           exc_req;
type_scr1_exc_code_e            exc_code;
logic                           ifu_fault_rvi_hi;
`ifndef SCR1_CLKCTRL_EN
logic                           wfi_halted;      // 1 - halted after WFI retirement
`endif // SCR1_CLKCTRL_EN
logic                           wfi_halt_cond;
logic                           wfi_run_cond;
logic                           wfi_run_start;

// PC signals
logic [3:0]                     init_pc_v;
logic                           init_pc;
logic [`SCR1_XLEN-1:0]          inc_pc;

`ifdef SCR1_DBGC_EN
logic                           exu_exc_req_r;
`endif // SCR1_DBGC_EN


//-------------------------------------------------------------------------------
// Instruction queue
//-------------------------------------------------------------------------------
`ifndef SCR1_EXU_STAGE_BYPASS

assign queue_barrier    =   wfi_halted | wfi_run2halt | wfi_run_start
`ifdef SCR1_DBGC_EN
                            | dbg_halted | dbg_run2halt | (dbg_run_start & ~fetch_pbuf)
`endif // SCR1_DBGC_EN
;
assign exu2idu_rdy      = exu_rdy & ~queue_barrier;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        exu_queue_vd <= 1'b0;
    end else begin
        if (queue_barrier) begin
            exu_queue_vd <= 1'b0;
        end else if (exu_rdy) begin
            exu_queue_vd <= idu2exu_req & ~new_pc_req;
        end
    end
end

always_ff @(posedge clk) begin
    if (exu2idu_rdy & idu2exu_req) begin
        exu_queue.instr_rvc      <= idu2exu_cmd.instr_rvc;
        exu_queue.ialu_op        <= idu2exu_cmd.ialu_op;
        exu_queue.ialu_cmd       <= idu2exu_cmd.ialu_cmd;
        exu_queue.sum2_op        <= idu2exu_cmd.sum2_op;
        exu_queue.lsu_cmd        <= idu2exu_cmd.lsu_cmd;
        exu_queue.csr_op         <= idu2exu_cmd.csr_op;
        exu_queue.csr_cmd        <= idu2exu_cmd.csr_cmd;
        exu_queue.rd_wb_sel      <= idu2exu_cmd.rd_wb_sel;
        exu_queue.jump_req       <= idu2exu_cmd.jump_req;
        exu_queue.branch_req     <= idu2exu_cmd.branch_req;
        exu_queue.mret_req       <= idu2exu_cmd.mret_req;
        exu_queue.fencei_req     <= idu2exu_cmd.fencei_req;
        exu_queue.wfi_req        <= idu2exu_cmd.wfi_req;
        exu_queue.exc_req        <= idu2exu_cmd.exc_req;
        exu_queue.exc_code       <= idu2exu_cmd.exc_code;
        idu2exu_use_rs1_r        <= idu2exu_use_rs1;
        idu2exu_use_rs2_r        <= idu2exu_use_rs2;
        if (idu2exu_use_rs1) begin
            exu_queue.rs1_addr   <= idu2exu_cmd.rs1_addr;
        end
        if (idu2exu_use_rs2) begin
            exu_queue.rs2_addr   <= idu2exu_cmd.rs2_addr;
        end
        if (idu2exu_use_rd)  begin
            exu_queue.rd_addr    <= idu2exu_cmd.rd_addr;
        end
        if (idu2exu_use_imm) begin
            exu_queue.imm        <= idu2exu_cmd.imm;
        end
    end
end

`else // ~SCR1_EXU_STAGE_BYPASS

assign queue_barrier    =   wfi_halted | wfi_run_start
`ifdef SCR1_DBGC_EN
                            | dbg_halted | (dbg_run_start & ~fetch_pbuf)
`endif // SCR1_DBGC_EN
;
assign exu2idu_rdy      = exu_rdy & ~queue_barrier;
assign exu_queue_vd     = idu2exu_req & ~queue_barrier;
assign exu_queue        = idu2exu_cmd;

`endif // ~SCR1_EXU_STAGE_BYPASS


`ifdef SCR1_BRKM_EN
//-------------------------------------------------------------------------------
// Interface to Trigger debug Unit (TDU)
//-------------------------------------------------------------------------------

// Instruction monitor
assign exu2tdu_i_mon.vd     = exu_queue_vd;
assign exu2tdu_i_mon.req    = instret;
assign exu2tdu_i_mon.addr   = curr_pc;

always_comb begin
    exu2tdu_bp_retire = '0;
    if (exu_queue_vd) begin
        exu2tdu_bp_retire = tdu2exu_i_match;
        if (lsu_req) begin
            exu2tdu_bp_retire[SCR1_TDU_MTRIG_NUM-1:0] |= tdu2lsu_d_match;
        end
    end
end
`endif // SCR1_BRKM_EN


//-------------------------------------------------------------------------------
// Operand Fetch
//-------------------------------------------------------------------------------
always_comb begin
    // IALU
    if (exu_queue.ialu_op == SCR1_IALU_OP_REG_REG) begin
        ialu_op1 = mprf2exu_rs1_data;
        ialu_op2 = mprf2exu_rs2_data;
    end else begin
        ialu_op1 = mprf2exu_rs1_data;
        ialu_op2 = exu_queue.imm;
    end
`ifdef SCR1_RVM_EXT
    ialu_op1 = ialu_vd ? ialu_op1 : '0;
    ialu_op2 = ialu_vd ? ialu_op2 : '0;
`endif // SCR1_RVM_EXT
    // SUM2
    if (exu_queue.sum2_op == SCR1_SUM2_OP_REG_IMM) begin
        ialu_sum2_op1 = mprf2exu_rs1_data;
        ialu_sum2_op2 = exu_queue.imm;
    end else begin
        ialu_sum2_op1 = curr_pc;
        ialu_sum2_op2 = exu_queue.imm;
    end
end

`ifdef SCR1_EXU_STAGE_BYPASS
assign exu2mprf_rs1_addr    = (exu_queue_vd & idu2exu_use_rs1) ? `SCR1_MPRF_ADDR_WIDTH'(exu_queue.rs1_addr) : '0;
assign exu2mprf_rs2_addr    = (exu_queue_vd & idu2exu_use_rs2) ? `SCR1_MPRF_ADDR_WIDTH'(exu_queue.rs2_addr) : '0;
`else // SCR1_EXU_STAGE_BYPASS
assign exu2mprf_rs1_addr    = (exu_queue_vd & idu2exu_use_rs1_r) ? `SCR1_MPRF_ADDR_WIDTH'(exu_queue.rs1_addr) : '0;
assign exu2mprf_rs2_addr    = (exu_queue_vd & idu2exu_use_rs2_r) ? `SCR1_MPRF_ADDR_WIDTH'(exu_queue.rs2_addr) : '0;
`endif // SCR1_EXU_STAGE_BYPASS


//-------------------------------------------------------------------------------
// Integer Arithmetic Logic Unit (IALU)
//-------------------------------------------------------------------------------
`ifdef SCR1_RVM_EXT
assign ialu_vd  = exu_queue_vd & (exu_queue.ialu_cmd != SCR1_IALU_CMD_NONE)
`ifdef SCR1_BRKM_EN
                & ~tdu2exu_i_x_req
`endif // SCR1_BRKM_EN
                ;
`endif // SCR1_RVM_EXT

scr1_pipe_ialu i_ialu(
`ifdef SCR1_RVM_EXT
    // Common
    .clk                (clk),
    .rst_n              (rst_n),
    .ialu_vd            (ialu_vd),
    .ialu_rdy           (ialu_rdy),
`endif // SCR1_RVM_EXT

    // IALU
    .ialu_op1           (ialu_op1),
    .ialu_op2           (ialu_op2),
    .ialu_cmd           (exu_queue.ialu_cmd),
    .ialu_res           (ialu_res),
    .ialu_cmp           (ialu_cmp),

    // SUM2
    .ialu_sum2_op1      (ialu_sum2_op1),
    .ialu_sum2_op2      (ialu_sum2_op2),
    .ialu_sum2_res      (ialu_sum2_res)
);


//-------------------------------------------------------------------------------
// Load/Store
//-------------------------------------------------------------------------------
assign lsu_req  = ((exu_queue.lsu_cmd != SCR1_LSU_CMD_NONE) & exu_queue_vd);

scr1_pipe_lsu i_lsu(
    .rst_n              (rst_n),
    .clk                (clk),

    .exu2lsu_req        (lsu_req),              // Request to LSU
    .exu2lsu_cmd        (exu_queue.lsu_cmd),    // LSU command
    .exu2lsu_addr       (ialu_sum2_res),        // DMEM address
    .exu2lsu_s_data     (mprf2exu_rs2_data),    // Data for store to DMEM
    .lsu2exu_rdy        (lsu_rdy),              // LSU ready
    .lsu2exu_l_data     (lsu_l_data),           // Loaded data form DMEM
    .lsu2exu_exc        (lsu_exc),              // LSU exception
    .lsu2exu_exc_code   (lsu_exc_code),         // LSU exception code

`ifdef SCR1_BRKM_EN
    .lsu2tdu_d_mon      (lsu2tdu_d_mon),
    .tdu2lsu_i_x_req    (tdu2lsu_i_x_req),
    .tdu2lsu_d_x_req    (tdu2lsu_d_x_req),
`endif // SCR1_BRKM_EN

    .lsu2dmem_req       (exu2dmem_req),         // DMEM request
    .lsu2dmem_cmd       (exu2dmem_cmd),         // DMEM command
    .lsu2dmem_width     (exu2dmem_width),       // DMEM width
    .lsu2dmem_addr      (exu2dmem_addr),        // DMEM address
    .lsu2dmem_wdata     (exu2dmem_wdata),       // DMEM write data
    .dmem2lsu_req_ack   (dmem2exu_req_ack),     // DMEM request acknowledge
    .dmem2lsu_rdata     (dmem2exu_rdata),       // DMEM read data
    .dmem2lsu_resp      (dmem2exu_resp)         // DMEM response
);


//-------------------------------------------------------------------------------
// CSR logic
//-------------------------------------------------------------------------------
always_comb begin
    if (exu_queue.csr_op == SCR1_CSR_OP_REG) begin
        exu2csr_w_data = mprf2exu_rs1_data;
    end else begin
        exu2csr_w_data = {'0, exu_queue.rs1_addr};    // zimm
    end
end

always_comb begin
    exu2csr_r_req    = 1'b0;
    exu2csr_w_req    = 1'b0;
    if (exu_queue_vd) begin
        case (exu_queue.csr_cmd)
            SCR1_CSR_CMD_WRITE  : begin
                exu2csr_r_req   = |exu_queue.rd_addr;
                exu2csr_w_req   = (csr_access == SCR1_CSR_INIT);
            end
            SCR1_CSR_CMD_SET,
            SCR1_CSR_CMD_CLEAR  : begin
                exu2csr_r_req   = 1'b1;
                exu2csr_w_req   = (|exu_queue.rs1_addr) & (csr_access == SCR1_CSR_INIT);
            end
            default : begin end
        endcase
    end // exu_queue_vd
`ifdef SCR1_BRKM_EN
    if (tdu2exu_i_x_req) begin
        exu2csr_r_req   = 1'b0;
        exu2csr_w_req   = 1'b0;
    end
`endif // SCR1_BRKM_EN
end

assign exu2csr_rw_addr  = exu_queue.imm[SCR1_CSR_ADDR_WIDTH-1:0];
assign exu2csr_w_cmd    = exu_queue.csr_cmd;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        csr_access  <= SCR1_CSR_INIT;
    end else begin
        if (csr_access == SCR1_CSR_INIT) begin
            if (csr2exu_mstatus_mie_up) begin
                csr_access  <= SCR1_CSR_RDY;
            end
        end else begin // SCR1_CSR_RDY
            csr_access  <= SCR1_CSR_INIT;
        end
    end
end

//-------------------------------------------------------------------------------
// Exception/MRET
//-------------------------------------------------------------------------------

`ifndef SCR1_RVC_EXT
// Instruction fetch misalign (jump/branch)
logic                   jb_misalign;
logic [`SCR1_XLEN-1:0]  tmp_new_pc;

assign tmp_new_pc   = ialu_sum2_res & SCR1_JUMP_MASK;
assign jb_misalign  = exu_queue_vd & (exu_queue.jump_req | (exu_queue.branch_req & ialu_cmp)) & |tmp_new_pc[1:0];
`endif // ~SCR1_RVC_EXT

// Exception request
assign exc_req  = exu_queue_vd & (
                    exu_queue.exc_req
                    | lsu_exc
                    | csr2exu_rw_exc
`ifndef SCR1_RVC_EXT
                    | jb_misalign
`endif // ~SCR1_RVC_EXT
`ifdef SCR1_BRKM_EN
                    | brkpt_hw
`endif // SCR1_BRKM_EN
                );

// Exception code
always_comb begin
    case (1'b1)
`ifdef SCR1_BRKM_EN
        // Hardware breakpoint has the highest priority
        brkpt_hw            : exc_code = SCR1_EXC_CODE_BREAKPOINT;
`endif // SCR1_BRKM_EN
        exu_queue.exc_req   : exc_code = exu_queue.exc_code;
        lsu_exc             : exc_code = lsu_exc_code;
        csr2exu_rw_exc      : exc_code = SCR1_EXC_CODE_ILLEGAL_INSTR;
`ifndef SCR1_RVC_EXT
        jb_misalign         : exc_code = SCR1_EXC_CODE_INSTR_MISALIGN;
`endif // ~SCR1_RVC_EXT
        default             : exc_code = SCR1_EXC_CODE_ECALL_M;
    endcase // 1'b1
end

assign ifu_fault_rvi_hi     = exu_queue.instr_rvc;

// Trap value
always_comb begin
    case (exc_code)
`ifndef SCR1_RVC_EXT
        SCR1_EXC_CODE_INSTR_MISALIGN        : exu2csr_trap_val  = tmp_new_pc;
`endif // SCR1_RVC_EXT
        SCR1_EXC_CODE_INSTR_ACCESS_FAULT    : exu2csr_trap_val  = ifu_fault_rvi_hi ? inc_pc : curr_pc;
                                                                // inc_pc is pc+2 if ifu_fault_rvi_hi==1
                                                                // so it points to the upper half of the
                                                                // faulty RVI instruction
`ifdef SCR1_MTVAL_ILLEGAL_INSTR_EN
        SCR1_EXC_CODE_ILLEGAL_INSTR         : exu2csr_trap_val  = exu_queue.exc_req ?
                                                                exu_queue.imm :
                                                                {   exu2csr_rw_addr,            // CSR address
                                                                    5'(exu_queue.rs1_addr),     // rs1 / zimm
                                                                    exu_queue.imm[14:12],       // funct3
                                                                    5'(exu_queue.rd_addr),      // rd
                                                                    SCR1_OPCODE_SYSTEM,
                                                                    SCR1_INSTR_RVI
                                                                };
`else // SCR1_MTVAL_ILLEGAL_INSTR_EN
        SCR1_EXC_CODE_ILLEGAL_INSTR         : exu2csr_trap_val  = '0;
`endif // SCR1_MTVAL_ILLEGAL_INSTR_EN
`ifdef SCR1_BRKM_EN
        SCR1_EXC_CODE_BREAKPOINT            : begin
            if (tdu2exu_i_x_req)           exu2csr_trap_val    = curr_pc;
            else if (tdu2lsu_d_x_req)      exu2csr_trap_val    = ialu_sum2_res;
            else                            exu2csr_trap_val    = '0;
        end
`endif // SCR1_BRKM_EN
        SCR1_EXC_CODE_LD_ADDR_MISALIGN,
        SCR1_EXC_CODE_LD_ACCESS_FAULT,
        SCR1_EXC_CODE_ST_ADDR_MISALIGN,
        SCR1_EXC_CODE_ST_ACCESS_FAULT       : exu2csr_trap_val  = ialu_sum2_res;
        default                             : exu2csr_trap_val  = '0;
    endcase // exc_code
end

// MRET
assign exu2csr_mret_instr = exu_queue_vd & exu_queue.mret_req
`ifdef SCR1_BRKM_EN
    & ~tdu2exu_i_x_req
`endif // SCR1_BRKM_EN
`ifdef SCR1_DBGC_EN
    & ~dbg_halted
`endif // SCR1_DBGC_EN
    ;

assign exu2csr_exc_code     = exc_code;

//-------------------------------------------------------------------------------
// Update PC
//-------------------------------------------------------------------------------
`ifdef SCR1_RVC_EXT
assign inc_pc       = curr_pc + (exu_queue.instr_rvc ? `SCR1_XLEN'd2 : `SCR1_XLEN'd4);
`else // ~SCR1_RVC_EXT
assign inc_pc       = curr_pc + `SCR1_XLEN'd4;
`endif // ~SCR1_RVC_EXT

assign new_pc_req   = init_pc                                      // reset
                    | exu2csr_take_irq
                    | exu2csr_take_exc
                    | (exu2csr_mret_instr & ~csr2exu_mstatus_mie_up)
                    | (exu_queue_vd & exu_queue.fencei_req)         // FENCE.I
                    | ((wfi_run_start)                              // WFI halt exit
`ifdef SCR1_CLKCTRL_EN
                        & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                        )
`ifdef SCR1_DBGC_EN
                    | (dbg_run_start & ~fetch_pbuf)                 // debug halt exit to RUN state
`endif // SCR1_DBGC_EN
                    | (exu_queue_vd & (exu_queue.jump_req | (exu_queue.branch_req & ialu_cmp)));    // jump / branch

assign exu2csr_take_exc     = exc_req
`ifdef SCR1_DBGC_EN
                            & ~dbg_halted
`endif // SCR1_DBGC_EN
                            ;
assign exu2csr_mret_update  = exu2csr_mret_instr & (csr_access == SCR1_CSR_INIT);
assign exu2csr_take_irq     = csr2exu_irq & ~exu_busy
`ifdef SCR1_DBGC_EN
                            & ~exu_irq_dsbl
                            & ~dbg_halted
`endif // SCR1_DBGC_EN
`ifdef SCR1_CLKCTRL_EN
                            & clk_pipe_en
`endif // SCR1_CLKCTRL_EN
                            ;


always_comb begin
    case (1'b1)
        init_pc                 : new_pc = SCR1_RST_VECTOR;
        exu2csr_take_exc,
        exu2csr_take_irq,
        exu2csr_mret_instr      : new_pc = csr2exu_new_pc;
`ifdef SCR1_DBGC_EN
        (dbg_run_start & ~fetch_pbuf): new_pc = dbg_new_pc;
`endif // SCR1_DBGC_EN
        wfi_run_start           : new_pc = curr_pc;
        exu_queue.fencei_req    : new_pc = inc_pc;
        default                 : new_pc = ialu_sum2_res & SCR1_JUMP_MASK;
    endcase
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        init_pc_v <= '0;
    end else begin
        if (~&init_pc_v) begin
            init_pc_v <= {init_pc_v[2:0], 1'b1};
        end
    end
end

assign init_pc = ~init_pc_v[3] & init_pc_v[2];

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        curr_pc    <= SCR1_RST_VECTOR;
    end else begin
        if ((instret | exu2csr_take_irq
`ifdef SCR1_DBGC_EN
        | (dbg_run_start & ~fetch_pbuf))
        & (~exu_pc_advmt_dsbl & ~exu_no_commit
`endif // SCR1_DBGC_EN
        )) begin
            if (new_pc_req) begin
                curr_pc <= new_pc;
            end else begin
                curr_pc[5:0] <= inc_pc[5:0];
                if (inc_pc[6] ^ curr_pc[6]) begin
                    curr_pc[`SCR1_XLEN-1:6] <= inc_pc[`SCR1_XLEN-1:6];
                end
            end
        end // update PC
    end
end

// PC to be loaded on MRET from interrupt trap
assign next_pc  = (exu_queue_vd)
                ? ((exu_queue.jump_req | (exu_queue.branch_req & ialu_cmp))
                    ? (ialu_sum2_res & SCR1_JUMP_MASK)
                    : (inc_pc))
                : (curr_pc);



`ifdef SCR1_DBGC_EN
//-------------------------------------------------------------------------------
// Debug, misc control logic
//-------------------------------------------------------------------------------
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        exu_exc_req_r   <= 1'b0;
    end else begin
        if (dbg_halt2run) begin
            exu_exc_req_r   <= 1'b0;
        end else if (instret) begin
            exu_exc_req_r   <= exc_req;
        end
    end
end

`endif // SCR1_DBGC_EN

assign exu_busy             = exu_queue_vd & ~exu_rdy;
`ifdef SCR1_DBGC_EN
assign exu_exc_req          = exu_queue_vd ? exc_req : exu_exc_req_r;
`else // SCR1_DBGC_EN
assign exu_exc_req          = exc_req;
`endif // SCR1_DBGC_EN
assign brkpt                = exu_queue_vd & (exu_queue.exc_code == SCR1_EXC_CODE_BREAKPOINT);
`ifdef SCR1_BRKM_EN
assign brkpt_hw             = tdu2exu_i_x_req | tdu2lsu_d_x_req;
`endif // SCR1_BRKM_EN
assign exu_init_pc          = init_pc;
assign instret              = exu_queue_vd & exu_rdy;
assign instret_nexc         = instret & ~exc_req;


//-------------------------------------------------------------------------------
// Write back to MPRF
//-------------------------------------------------------------------------------
always_comb begin
    exu2mprf_w_req  = (exu_queue.rd_wb_sel != SCR1_RD_WB_NONE) & exu_queue_vd & ~exc_req
`ifdef SCR1_DBGC_EN
                    & ~exu_no_commit
`endif // SCR1_DBGC_EN
                    & ((exu_queue.rd_wb_sel == SCR1_RD_WB_CSR) ? (csr_access == SCR1_CSR_INIT) : exu_rdy);
    exu2mprf_rd_addr = `SCR1_MPRF_ADDR_WIDTH'(exu_queue.rd_addr);
    case (exu_queue.rd_wb_sel)
        SCR1_RD_WB_SUM2     : exu2mprf_rd_data = ialu_sum2_res;
        SCR1_RD_WB_IMM      : exu2mprf_rd_data = exu_queue.imm;
        SCR1_RD_WB_INC_PC   : exu2mprf_rd_data = inc_pc;
        SCR1_RD_WB_LSU      : exu2mprf_rd_data = lsu_l_data;
        SCR1_RD_WB_CSR      : exu2mprf_rd_data = csr2exu_r_data;
        default             : exu2mprf_rd_data = ialu_res;      // IALU by default
    endcase
end


//-------------------------------------------------------------------------------
// Execution ready
//-------------------------------------------------------------------------------
always_comb begin
    case (1'b1)
        lsu_req                 : exu_rdy = lsu_rdy | lsu_exc;
`ifdef SCR1_RVM_EXT
        ialu_vd                 : exu_rdy = ialu_rdy;
`endif // SCR1_RVM_EXT
        csr2exu_mstatus_mie_up  : exu_rdy = 1'b0;
        default                 : exu_rdy = 1'b1;
    endcase
end


//-------------------------------------------------------------------------------
// WFI instruction
//-------------------------------------------------------------------------------
assign wfi_halt_cond    = ~csr2exu_ip_ie
                        & ((exu_queue_vd & exu_queue.wfi_req) | wfi_run_start)
`ifdef SCR1_DBGC_EN
                        & ~exu_no_commit & ~exu_dmode_sstep_en & ~dbg_run2halt
`endif // SCR1_DBGC_EN
                        ;
assign wfi_run_cond     = csr2exu_ip_ie;

assign wfi_run2halt     = ~wfi_halted & wfi_halt_cond;

always_ff @(negedge rst_n,
`ifndef SCR1_CLKCTRL_EN
posedge clk
`else // SCR1_CLKCTRL_EN
posedge clk_alw_on
`endif // SCR1_CLKCTRL_EN
) begin
    if (~rst_n) begin
        wfi_run_start  <= 1'b0;
    end else begin
        wfi_run_start <= (wfi_halted & wfi_run_cond & ~exu2csr_take_irq);
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
        wfi_halted  <= 1'b0;
    end else begin
        if (~wfi_halted & wfi_halt_cond) begin
            wfi_halted  <= 1'b1;
        end else if (wfi_halted & (wfi_run_cond
`ifdef SCR1_DBGC_EN
                                    | dbg_halt2run
`endif // SCR1_DBGC_EN
        )) begin
            wfi_halted  <= 1'b0;
        end
    end
end


`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Tracelog signals
//-------------------------------------------------------------------------------
logic [`SCR1_XLEN-1:0]      update_pc;
logic                       update_pc_en;

assign update_pc_en = (init_pc | instret | exu2csr_take_irq)
`ifdef SCR1_DBGC_EN
                    & ~exu_pc_advmt_dsbl & ~exu_no_commit
`endif // SCR1_DBGC_EN
                    ;
assign update_pc    = new_pc_req ? new_pc : inc_pc;

`ifndef VERILATOR
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_EXU_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({idu2exu_req, csr2exu_irq, csr2exu_ip_ie, lsu_req, lsu_rdy, exc_req})
    ) else $error("EXU Error: unknown control values");

SCR1_SVA_EXU_XCHECK_QUEUE : assert property (
    @(negedge clk) disable iff (~rst_n)
    idu2exu_req |-> !$isunknown(idu2exu_cmd)
    ) else $error("EXU Error: unknown values in queue");

SCR1_SVA_EXU_XCHECK_CSR_RDATA : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2csr_r_req |-> !$isunknown({csr2exu_r_data, csr2exu_rw_exc})
    ) else $error("EXU Error: unknown values from CSR");

// Behavior checks

SCR1_SVA_EXU_ONEHOT : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({exu_queue.jump_req, exu_queue.branch_req, lsu_req})
    ) else $error("EXU Error: illegal combination of control signals");

SCR1_SVA_EXU_ONEHOT_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu_queue_vd |->
    $onehot0({exu_queue.exc_req, lsu_exc, csr2exu_rw_exc
`ifndef SCR1_RVC_EXT
    , jb_misalign
`endif
    })
    ) else $error("EXU Error: exceptions $onehot0 failed");

`endif // VERILATOR

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_exu

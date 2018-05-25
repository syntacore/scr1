/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_lsu.sv>
/// @brief      Load/Store Unit (LSU)
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"
`ifdef SCR1_BRKM_EN
`include "scr1_brkm.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_lsu (
    // Common
    input   logic                               rst_n,
    input   logic                               clk,

    // EXU <-> LSU interface
    input   logic                               exu2lsu_req,            // Request to LSU
    input   type_scr1_lsu_cmd_sel_e             exu2lsu_cmd,            // LSU command
    input   logic [`SCR1_XLEN-1:0]              exu2lsu_addr,           // Address of DMEM
    input   logic [`SCR1_XLEN-1:0]              exu2lsu_s_data,         // Data for store
    output  logic                               lsu2exu_rdy,            // LSU received DMEM response
    output  logic [`SCR1_XLEN-1:0]              lsu2exu_l_data,         // Load data
    output  logic                               lsu2exu_exc,            // Exception from LSU
    output  type_scr1_exc_code_e                lsu2exu_exc_code,       // Exception code
    output  logic                               lsu_busy,

    // BRKM <-> LSU interface
`ifdef SCR1_BRKM_EN
    output  type_scr1_brkm_lsu_mon_s            lsu2brkm_d_mon,
    input   logic                               brkm2lsu_i_x_req,
    input   logic                               brkm2lsu_d_x_req,
`endif // SCR1_BRKM_EN

    // Data memory interface
    output  logic                               lsu2dmem_req,
    output  type_scr1_mem_cmd_e                 lsu2dmem_cmd,
    output  type_scr1_mem_width_e               lsu2dmem_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]       lsu2dmem_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]       lsu2dmem_wdata,
    input   logic                               dmem2lsu_req_ack,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]       dmem2lsu_rdata,
    input   type_scr1_mem_resp_e                dmem2lsu_resp
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef enum logic {SCR1_FSM_IDLE, SCR1_FSM_BUSY} type_scr1_lsu_fsm_e;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
type_scr1_lsu_fsm_e         fsm;
type_scr1_lsu_cmd_sel_e     lsu_cmd_r;
logic                       dmem_resp_ok;
logic                       dmem_resp_er;
logic                       l_misalign;
logic                       s_misalign;
`ifdef SCR1_BRKM_EN
logic                       lsu_hwbrk;
`endif // SCR1_BRKM_EN


//-------------------------------------------------------------------------------
// Main logic
//-------------------------------------------------------------------------------
assign dmem_resp_ok = (dmem2lsu_resp == SCR1_MEM_RESP_RDY_OK);
assign dmem_resp_er = (dmem2lsu_resp == SCR1_MEM_RESP_RDY_ER);

//-------------------------------------------------------------------------------
// FSM
//-------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        fsm         <= SCR1_FSM_IDLE;
        lsu_cmd_r   <= SCR1_LSU_CMD_NONE;
    end else begin
        case (fsm)
            SCR1_FSM_IDLE   : begin
                if (exu2lsu_req & dmem2lsu_req_ack & ~lsu2exu_exc) begin
                    fsm         <= SCR1_FSM_BUSY;
                    lsu_cmd_r   <= exu2lsu_cmd;
                end
            end
            SCR1_FSM_BUSY   : begin
                if (dmem_resp_ok | dmem_resp_er) begin
                    fsm     <= SCR1_FSM_IDLE;
                end
            end
        endcase // fsm
    end
end

assign lsu_busy = (fsm == SCR1_FSM_BUSY);

//-------------------------------------------------------------------------------
// Load / store address misaligned exception
//-------------------------------------------------------------------------------
always_comb begin
    l_misalign = 1'b0;
    s_misalign = 1'b0;
    if (exu2lsu_req) begin
        case (exu2lsu_cmd)
            SCR1_LSU_CMD_LH,
            SCR1_LSU_CMD_LHU    : l_misalign = exu2lsu_addr[0];
            SCR1_LSU_CMD_LW     : l_misalign = |exu2lsu_addr[1:0];
            SCR1_LSU_CMD_SH     : s_misalign = exu2lsu_addr[0];
            SCR1_LSU_CMD_SW     : s_misalign = |exu2lsu_addr[1:0];
            default : begin end
        endcase // exu2lsu_cmd
    end
end

//-------------------------------------------------------------------------------
// LSU <-> EXU interface
//-------------------------------------------------------------------------------
assign lsu2exu_rdy  =   (dmem_resp_ok | dmem_resp_er);
assign lsu2exu_exc  =   dmem_resp_er | l_misalign | s_misalign
`ifdef SCR1_BRKM_EN
                        | lsu_hwbrk
`endif // SCR1_BRKM_EN
;

//-------------------------------------------------------------------------------
// Exception code
//-------------------------------------------------------------------------------
always_comb begin
    case (1'b1)
        dmem_resp_er    : begin
            case (lsu_cmd_r)
                SCR1_LSU_CMD_LB,
                SCR1_LSU_CMD_LH,
                SCR1_LSU_CMD_LW,
                SCR1_LSU_CMD_LBU,
                SCR1_LSU_CMD_LHU    : lsu2exu_exc_code = SCR1_EXC_CODE_LD_ACCESS_FAULT;
                SCR1_LSU_CMD_SB,
                SCR1_LSU_CMD_SH,
                SCR1_LSU_CMD_SW     : lsu2exu_exc_code = SCR1_EXC_CODE_ST_ACCESS_FAULT;
                // Impossible
                default             : lsu2exu_exc_code = SCR1_EXC_CODE_INSTR_MISALIGN;
            endcase
        end // dmem_resp_er
`ifdef SCR1_BRKM_EN
        lsu_hwbrk                   : lsu2exu_exc_code = SCR1_EXC_CODE_BREAKPOINT;
`endif // SCR1_BRKM_EN
        l_misalign                  : lsu2exu_exc_code = SCR1_EXC_CODE_LD_ADDR_MISALIGN;
        s_misalign                  : lsu2exu_exc_code = SCR1_EXC_CODE_ST_ADDR_MISALIGN;
        default                     : lsu2exu_exc_code = SCR1_EXC_CODE_INSTR_MISALIGN;
    endcase // 1'b1
end

//-------------------------------------------------------------------------------
// Sign-extend or zero-extend received data
//-------------------------------------------------------------------------------
always_comb begin
    case (lsu_cmd_r)
        SCR1_LSU_CMD_LW     : lsu2exu_l_data = dmem2lsu_rdata;
        SCR1_LSU_CMD_LH     : lsu2exu_l_data = $signed  (dmem2lsu_rdata[15:0]);
        SCR1_LSU_CMD_LHU    : lsu2exu_l_data = $unsigned(dmem2lsu_rdata[15:0]);
        SCR1_LSU_CMD_LB     : lsu2exu_l_data = $signed  (dmem2lsu_rdata[7:0]);
        SCR1_LSU_CMD_LBU    : lsu2exu_l_data = $unsigned(dmem2lsu_rdata[7:0]);
        default             : lsu2exu_l_data = '0;
    endcase // lsu_cmd_r
end

//-------------------------------------------------------------------------------
// Data memory interface
//-------------------------------------------------------------------------------
assign lsu2dmem_req     = exu2lsu_req & ~lsu2exu_exc & (fsm == SCR1_FSM_IDLE);
assign lsu2dmem_addr    = exu2lsu_addr;
assign lsu2dmem_wdata   = exu2lsu_s_data;

always_comb begin
    case (exu2lsu_cmd)
        SCR1_LSU_CMD_LB,
        SCR1_LSU_CMD_LBU    : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_RD;
            lsu2dmem_width  = SCR1_MEM_WIDTH_BYTE;
        end
        SCR1_LSU_CMD_LH,
        SCR1_LSU_CMD_LHU    : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_RD;
            lsu2dmem_width  = SCR1_MEM_WIDTH_HWORD;
        end
        SCR1_LSU_CMD_LW     : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_RD;
            lsu2dmem_width  = SCR1_MEM_WIDTH_WORD;
        end
        SCR1_LSU_CMD_SB     : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_WR;
            lsu2dmem_width  = SCR1_MEM_WIDTH_BYTE;
        end
        SCR1_LSU_CMD_SH     : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_WR;
            lsu2dmem_width  = SCR1_MEM_WIDTH_HWORD;
        end
        SCR1_LSU_CMD_SW     : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_WR;
            lsu2dmem_width  = SCR1_MEM_WIDTH_WORD;
        end
        default             : begin
            lsu2dmem_cmd    = SCR1_MEM_CMD_RD;
            lsu2dmem_width  = SCR1_MEM_WIDTH_WORD;
        end
    endcase // exu2lsu_cmd
end

`ifdef SCR1_BRKM_EN
//-------------------------------------------------------------------------------
// BRKM
//-------------------------------------------------------------------------------
assign lsu2brkm_d_mon.vd        = exu2lsu_req & (fsm == SCR1_FSM_IDLE) & ~brkm2lsu_i_x_req;
assign lsu2brkm_d_mon.addr      = exu2lsu_addr;
assign lsu2brkm_d_mon.load      = (lsu2dmem_cmd == SCR1_MEM_CMD_RD);
assign lsu2brkm_d_mon.store     = (lsu2dmem_cmd == SCR1_MEM_CMD_WR);

always_comb begin
    case (lsu2dmem_width)
        SCR1_MEM_WIDTH_BYTE: begin
            lsu2brkm_d_mon.width = SCR1_OP_WIDTH_BYTE;
        end

        SCR1_MEM_WIDTH_HWORD: begin
            lsu2brkm_d_mon.width = SCR1_OP_WIDTH_HALF;
        end

        SCR1_MEM_WIDTH_WORD: begin
            lsu2brkm_d_mon.width = SCR1_OP_WIDTH_WORD;
        end

        default: begin
            lsu2brkm_d_mon.width = SCR1_OP_WIDTH_ERROR;
        end
    endcase
end

assign lsu_hwbrk    = (exu2lsu_req & brkm2lsu_i_x_req) | brkm2lsu_d_x_req;

`endif // SCR1_BRKM_EN

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_LSU_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2lsu_req, fsm
`ifdef SCR1_BRKM_EN
        , brkm2lsu_i_x_req, brkm2lsu_d_x_req
`endif // SCR1_BRKM_EN
    })
    ) else $error("LSU Error: unknown control value");

SCR1_SVA_LSU_XCHECK_CMD : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2lsu_req |-> !$isunknown({exu2lsu_cmd, exu2lsu_addr})
    ) else $error("LSU Error: exception code undefined");

SCR1_SVA_LSU_XCHECK_SDATA : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2lsu_req & (lsu2dmem_cmd == SCR1_MEM_CMD_WR)) |-> !$isunknown({exu2lsu_s_data})
    ) else $error("LSU Error: exception code undefined");

SCR1_SVA_LSU_XCHECK_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2exu_exc |-> !$isunknown(lsu2exu_exc_code)
    ) else $error("LSU Error: exception code undefined");

// Behavior checks

SCR1_SVA_LSU_EXC_ONEHOT : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({dmem_resp_er, l_misalign, s_misalign})
    ) else $error("LSU Error: more than one exception at a time");

SCR1_SVA_LSU_UNEXPECTED_DMEM_RESP : assert property (
    @(negedge clk) disable iff (~rst_n)
    (fsm == SCR1_FSM_IDLE) |-> ~(dmem_resp_ok | dmem_resp_er)
    ) else $error("LSU Error: not expecting memory response");

SCR1_SVA_LSU_REQ_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2exu_exc |-> exu2lsu_req
    ) else $error("LSU Error: impossible exception");

`ifdef SCR1_BRKM_EN
SCR1_COV_LSU_MISALIGN_BRKPT : cover property (
    @(negedge clk) disable iff (~rst_n)
    (l_misalign | s_misalign) & lsu_hwbrk
);
`endif // SCR1_BRKM_EN

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_lsu
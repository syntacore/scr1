/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_ialu.sv>
/// @brief      Integer Arithmetic Logic Unit (IALU)
///

`include "scr1_arch_description.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_search_ms1.svh"


module scr1_pipe_ialu (
`ifdef SCR1_RVM_EXT
    // Common
    input   logic                           clk,
    input   logic                           rst_n,
    input   logic                           ialu_vd,
    output  logic                           ialu_rdy,
`endif // SCR1_RVM_EXT
    output  logic                           ialu_busy,

    // IALU input
    input   logic [`SCR1_XLEN-1:0]          ialu_op1,
    input   logic [`SCR1_XLEN-1:0]          ialu_op2,
    input   type_scr1_ialu_cmd_sel_e        ialu_cmd,
    // IALU output
    output  logic [`SCR1_XLEN-1:0]          ialu_res,
    output  logic                           ialu_cmp,

    // SUM2 input
    input   logic [`SCR1_XLEN-1:0]          ialu_sum2_op1,
    input   logic [`SCR1_XLEN-1:0]          ialu_sum2_op2,
    // SUM2 output
    output  logic [`SCR1_XLEN-1:0]          ialu_sum2_res
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT
 `ifndef SCR1_FAST_MUL
localparam SCR1_IALU_MUL_WIDTH  = 1;
localparam SCR1_MUL_INIT_CNT    = (`SCR1_XLEN/SCR1_IALU_MUL_WIDTH)-1;
 `endif // ~SCR1_FAST_MUL
localparam SCR1_DIV_INIT_CNT    = `SCR1_XLEN-1;
`endif // SCR1_RVM_EXT

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef struct packed {
    logic       z;      // Zero
    logic       s;      // Sign
    logic       o;      // Overflow
    logic       c;      // Carry
} type_scr1_ialu_flags_s;

 `ifdef SCR1_RVM_EXT
typedef enum logic [1:0] {
    SCR1_IALU_FSM_IDLE,
    SCR1_IALU_FSM_ITER,
    SCR1_IALU_FSM_CORR
} type_scr1_ialu_fsm_state;

typedef enum logic [1:0] {
   SCR1_IALU_MDU_NONE,
   SCR1_IALU_MDU_MUL,
   SCR1_IALU_MDU_DIV
} type_scr1_ialu_mdu_cmd;
 `endif // SCR1_RVM_EXT

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT
type_scr1_ialu_fsm_state                    curr_state;     // Current FSM state
type_scr1_ialu_fsm_state                    next_state;     // Next FSM state
logic                                       iter_req;       // Request iterative stage
logic                                       iter_rdy;       // Request iterative stage
type_scr1_ialu_mdu_cmd                      mdu_cmd;        // MDU command: 00 - NONE, 01 - MUL, 10 - DIV
logic [1:0]                                 mul_cmd;        // MUL command: 00 - MUL, 01 - MULH, 10 - MULHSU, 11 - MULHU
logic [1:0]                                 div_cmd;        // DIV command: 00 - DIV, 01 - DIVU, 10 - REM,    11 - REMU
logic                                       corr_req;       // DIV correction request
`endif // SCR1_RVM_EXT

logic                                       sum1_sub;       // SUM1 operation: 0 - add, 1 - sub
logic [31:0]                                sum1_op1;       // SUM1 operand 1
logic [31:0]                                sum1_op2;       // SUM1 operand 2
logic [32:0]                                sum1_res;       // SUM1 result
type_scr1_ialu_flags_s                      sum1_flags;     // SUM1 flags

`ifdef SCR1_RVM_EXT
logic                                       sum2_sub;       // SUM2 operation: 0 - add, 1 - sub
logic signed [32:0]                         sum2_op1;       // SUM2 operand 1
 `ifdef SCR1_FAST_MUL
logic signed [32:0]                         sum2_op2;       // SUM2 operand 2
logic signed [32:0]                         sum2_res;       // SUM2 result
 `else // ~SCR1_FAST_MUL
logic signed [(32+SCR1_IALU_MUL_WIDTH)-1:0] sum2_op2;       // SUM2 operand 2
logic signed [(32+SCR1_IALU_MUL_WIDTH)-1:0] sum2_res;       // SUM2 result
 `endif // ~SCR1_FAST_MUL
`endif // SCR1_RVM_EXT

logic signed [31:0]                         shft_op1;       // SHIFT operand 1
logic [4:0]                                 shft_op2;       // SHIFT operand 2
logic [1:0]                                 shft_cmd;       // SHIFT command: 00 - logical left, 10 - logical right, 11 - arithmetical right
logic [31:0]                                shft_res;       // SHIFT result

`ifdef SCR1_RVM_EXT
logic signed [32:0]                         mul_op1;        // MUL operand 1
 `ifdef SCR1_FAST_MUL
logic signed [32:0]                         mul_op2;        // MUL operand 1
logic signed [63:0]                         mul_res;        // MUL result
 `else // ~SCR1_FAST_MUL
logic signed [SCR1_IALU_MUL_WIDTH:0]        mul_op2;        // MUL operand 2
logic signed [(32+SCR1_IALU_MUL_WIDTH)-1:0] mul_res;        // MUL result
 `endif // ~SCR1_FAST_MUL
`endif // SCR1_RVM_EXT

`ifdef SCR1_RVM_EXT
logic [4:0]                                 cnt_res;
logic [4:0]                                 cnt_res_reg;
logic [31:0]                                res32_1_reg;
logic [31:0]                                res32_1;
logic [31:0]                                res32_2;
logic [31:0]                                res32_2_reg;
logic                                       res32_1_c;
logic                                       res32_1_c_reg;
logic [31:0]                                res32_3;
logic [31:0]                                res32_3_reg;
`endif // SCR1_RVM_EXT


`ifdef SCR1_RVM_EXT
//-------------------------------------------------------------------------------
// Control State Machine
//-------------------------------------------------------------------------------
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        curr_state <= SCR1_IALU_FSM_IDLE;
    end else begin
        if (~ialu_vd) begin
            curr_state  <= SCR1_IALU_FSM_IDLE;
        end else begin
            curr_state  <= next_state;
        end
    end
end


always_comb begin
    next_state = curr_state;
    case (curr_state)
        SCR1_IALU_FSM_IDLE : begin
            // Switch to ITER if shift, mul, div
            if (iter_req) begin
                next_state = SCR1_IALU_FSM_ITER;
            end
        end
        SCR1_IALU_FSM_ITER : begin
            // End of ITER if calculation completed
            if (iter_rdy) begin
                // Switch to CORR if need correction
                if (corr_req) begin
                    next_state = SCR1_IALU_FSM_CORR;
                end else begin
                    next_state = SCR1_IALU_FSM_IDLE;
                end
            end
        end
        SCR1_IALU_FSM_CORR : begin
            next_state = SCR1_IALU_FSM_IDLE;
        end
    endcase
end

assign ialu_busy = ialu_vd & ~ialu_rdy;

`else // SCR1_RVM_EXT
assign ialu_busy = 1'b0;
`endif // SCR1_RVM_EXT

//-------------------------------------------------------------------------------
// SUM1 - main adder
//-------------------------------------------------------------------------------
always_comb begin
    // MUXs to SUM1
    sum1_sub    = (ialu_cmd != SCR1_IALU_CMD_ADD);
    sum1_op1    = ialu_op1;
    sum1_op2    = ialu_op2;
`ifdef SCR1_RVM_EXT
    case (mdu_cmd)
        SCR1_IALU_MDU_DIV : begin
            case (curr_state)
                SCR1_IALU_FSM_IDLE,
                SCR1_IALU_FSM_ITER : begin
                    sum1_sub    = 1'b1;
                    sum1_op1    = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? ($signed(SCR1_DIV_INIT_CNT))
                                    : ($signed({'0, cnt_res_reg}));
                    sum1_op2    = 32'sb1;
                end
                SCR1_IALU_FSM_CORR : begin
                    sum1_sub    = 1'b1;
                    sum1_op1    = '0;
                    sum1_op2    = $signed(res32_2_reg);
                end
            endcase
        end
 `ifndef SCR1_FAST_MUL
        SCR1_IALU_MDU_MUL : begin
            sum1_sub    = 1'b1;
            if (curr_state == SCR1_IALU_FSM_IDLE) begin
                sum1_op1    = ($signed(SCR1_MUL_INIT_CNT));
            end else begin
                sum1_op1    = $signed({'0, cnt_res_reg});
            end
            sum1_op2    = 32'sb1;
        end
 `endif // ~SCR1_FAST_MUL
        default : begin end
    endcase
`endif // SCR1_RVM_EXT

    // SUM1
    sum1_res     = (sum1_sub)
                        ? (sum1_op1 - sum1_op2)   // Subtraction and comparation
                        : (sum1_op1 + sum1_op2);  // Addition

    // FLAGS1 - flags for comparation (result of subtraction)
    sum1_flags.c = sum1_res[`SCR1_XLEN];
    sum1_flags.z = ~|sum1_res[`SCR1_XLEN-1:0];
    sum1_flags.s = sum1_res[`SCR1_XLEN-1];
    sum1_flags.o = (~sum1_op1[`SCR1_XLEN-1] &  sum1_op2[`SCR1_XLEN-1] &  sum1_res[`SCR1_XLEN-1]) |
                   ( sum1_op1[`SCR1_XLEN-1] & ~sum1_op2[`SCR1_XLEN-1] & ~sum1_res[`SCR1_XLEN-1]);
end


`ifdef SCR1_RVM_EXT
always_comb begin
    cnt_res     = sum1_res[4:0];
end
`endif // SCR1_RVM_EXT


//-------------------------------------------------------------------------------
// SUM2 - additional adder
//-------------------------------------------------------------------------------
`ifdef SCR1_RVM_EXT
always_comb begin
    sum2_sub    = 1'b0;
    sum2_op1    = $signed(ialu_sum2_op1);
    sum2_op2    = $signed(ialu_sum2_op2);
    case (mdu_cmd)
        SCR1_IALU_MDU_DIV : begin
            case (curr_state)
                SCR1_IALU_FSM_IDLE,
                SCR1_IALU_FSM_ITER : begin
                    logic           sgn;
                    logic           inv;
                    sgn         = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? (1'b0)
                                    : (~res32_2_reg[0]);
                    inv         = (~div_cmd[0] & (ialu_op1[31] ^ ialu_op2[31]));
                    sum2_sub    = ~inv ^ sgn;
                    sum2_op1    = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? $signed({(~div_cmd[0] & ialu_op1[31]), ialu_op1[31]})
                                    : $signed({res32_1_reg[31:0], res32_3_reg[31]});
                    sum2_op2    = $signed({(~div_cmd[0] & ialu_op2[31]), ialu_op2});
                end
                SCR1_IALU_FSM_CORR : begin
                    logic           sgn;
                    logic           inv;
                    sgn         = (~div_cmd[0] & ialu_op1[31]) ^ res32_1_c_reg;
                    inv         = (~div_cmd[0] & (ialu_op1[31] ^ ialu_op2[31]));
                    sum2_sub    = ~inv ^ sgn;
                    sum2_op1    = $signed({1'b0, res32_1_reg});
                    sum2_op2    = $signed({(~div_cmd[0] & ialu_op2[31]), ialu_op2});
                end
            endcase
        end
`ifndef SCR1_FAST_MUL
        SCR1_IALU_MDU_MUL : begin
            sum2_sub    = ~mul_cmd[1] & ialu_op2[31] & sum1_res[32];
            sum2_op1    = (curr_state == SCR1_IALU_FSM_IDLE)
                            ? ('0)
                            : ($signed({(~&mul_cmd & res32_1_reg[31]), res32_1_reg}));
            sum2_op2    = $signed(mul_res);
        end
`endif // SCR1_FAST_MUL
       default : begin end
   endcase
    sum2_res     = (sum2_sub)
                    ? (sum2_op1 - sum2_op2)   // Subtraction
                    : (sum2_op1 + sum2_op2);  // Addition
end
assign ialu_sum2_res = sum2_res[31:0];
`else // ~SCR1_RVM_EXT
assign ialu_sum2_res = ialu_sum2_op1 + ialu_sum2_op2;  // Addition
`endif // ~SCR1_RVM_EXT


//-------------------------------------------------------------------------------
// SHIFT
//-------------------------------------------------------------------------------
always_comb begin
    shft_op1    = ialu_op1;
    shft_op2    = ialu_op2[4:0];
    case (shft_cmd)
        2'b10   : shft_res = shft_op1  >> shft_op2;
        2'b11   : shft_res = shft_op1 >>> shft_op2;
        default : shft_res = shft_op1  << shft_op2;
    endcase
end


 `ifdef SCR1_RVM_EXT
//-------------------------------------------------------------------------------
// MUL - multiplier
//-------------------------------------------------------------------------------
always_comb begin
    mul_op1 = '0;
    mul_op2 = '0;
    mul_res = '0;
    if (mdu_cmd == SCR1_IALU_MDU_MUL) begin
        mul_op1 = $signed({(~&mul_cmd   & ialu_op1[31]), ialu_op1});
`ifdef SCR1_FAST_MUL
        mul_op2 = $signed({(~mul_cmd[1] & ialu_op2[31]), ialu_op2});
`else // ~SCR1_FAST_MUL
        mul_op2 = (curr_state == SCR1_IALU_FSM_IDLE)
                        ? ($signed({1'b0, ialu_op2[SCR1_IALU_MUL_WIDTH-1:0]}))
                        : ($signed({1'b0, res32_2_reg[SCR1_IALU_MUL_WIDTH-1:0]}));
`endif // ~SCR1_FAST_MUL
        mul_res = mul_op1 * mul_op2;
    end
end


//-------------------------------------------------------------------------------
// DIV - divider
//-------------------------------------------------------------------------------
always_comb begin
    res32_1     = '0;
    res32_2     = '0;
    res32_1_c   = '0;
    res32_3     = '0;
    case (mdu_cmd)
        SCR1_IALU_MDU_DIV : begin
            case (curr_state)
                SCR1_IALU_FSM_IDLE,
                SCR1_IALU_FSM_ITER : begin
                    logic [30:0]    prev_low;
                    logic           quo;
                    prev_low    = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? (ialu_op1[30:0])
                                    : (res32_3_reg[30:0]);
                    quo         = ~((~div_cmd[0] & ialu_op1[31]) ^ (sum2_res[32]))
                                  | ((~div_cmd[0] & ialu_op1[31]) & (~|{sum2_res, prev_low}));

                    {res32_1_c, res32_1}    = sum2_res;                 // Hight part of extended dividend (reminder)
                    res32_3     = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? ({ialu_op1[30:0], 1'b0})
                                    : ({res32_3_reg[30:0], 1'b0});      // Low part of extended dividend (reminder)
                    res32_2     = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? ({'0, quo})
                                    : ({res32_2_reg[32-2:0], quo});     // Quotient

                end
                default : begin end
            endcase
        end
`ifndef SCR1_FAST_MUL
        SCR1_IALU_MDU_MUL : begin
            {res32_1, res32_2}  = (curr_state == SCR1_IALU_FSM_IDLE)
                                    ? ({sum2_res, ialu_op2[31:SCR1_IALU_MUL_WIDTH]})
                                    : ({sum2_res, res32_2_reg[31:SCR1_IALU_MUL_WIDTH]});
        end
`endif // ~SCR1_FAST_MUL
        default : begin end
    endcase
end
`endif // SCR1_RVM_EXT


`ifdef SCR1_RVM_EXT
//-------------------------------------------------------------------------------
// FSM control signals
//-------------------------------------------------------------------------------
always_comb begin
    iter_req  = 1'b0;
    iter_rdy  = 1'b0;
    corr_req = (mdu_cmd == SCR1_IALU_MDU_DIV) & ((div_cmd == 2'b00) & (ialu_op1[31] ^ ialu_op2[31]) |
              (div_cmd[1] & |res32_1 & ((~div_cmd[0] & ialu_op1[31]) ^ res32_1_c)));
 `ifdef SCR1_FAST_MUL
    if (mdu_cmd == SCR1_IALU_MDU_DIV) begin
        iter_req  = |ialu_op1 & |ialu_op2 & (curr_state == SCR1_IALU_FSM_IDLE);
        iter_rdy  = sum1_flags.c & (curr_state == SCR1_IALU_FSM_ITER);
    end
 `else // ~SCR1_FAST_MUL
    if (mdu_cmd != SCR1_IALU_MDU_NONE) begin
        iter_req  = |ialu_op1 & |ialu_op2 & (curr_state == SCR1_IALU_FSM_IDLE);
        iter_rdy  = sum1_flags.c & (curr_state == SCR1_IALU_FSM_ITER);
    end
 `endif // ~SCR1_FAST_MUL
end
`endif // SCR1_RVM_EXT


//-------------------------------------------------------------------------------
// Operation result forming
//-------------------------------------------------------------------------------
always_comb begin
    ialu_res    = '0;
    ialu_cmp    = 1'b0;
    shft_cmd    = 2'b0;
`ifdef SCR1_RVM_EXT
    mdu_cmd     = SCR1_IALU_MDU_NONE;
    mul_cmd     = {((ialu_cmd == SCR1_IALU_CMD_MULHU) | (ialu_cmd == SCR1_IALU_CMD_MULHSU)),
                   ((ialu_cmd == SCR1_IALU_CMD_MULHU) | (ialu_cmd == SCR1_IALU_CMD_MULH))};
    div_cmd     = {((ialu_cmd == SCR1_IALU_CMD_REM)   | (ialu_cmd == SCR1_IALU_CMD_REMU)),
                   ((ialu_cmd == SCR1_IALU_CMD_REMU)  | (ialu_cmd == SCR1_IALU_CMD_DIVU))};
    ialu_rdy    = 1'b1;
`endif // SCR1_RVM_EXT

    case (ialu_cmd)
        SCR1_IALU_CMD_AND : begin
            ialu_res    = ialu_op1 & ialu_op2;
        end
        SCR1_IALU_CMD_OR : begin
            ialu_res    = ialu_op1 | ialu_op2;
        end
        SCR1_IALU_CMD_XOR : begin
            ialu_res    = ialu_op1 ^ ialu_op2;
        end
        SCR1_IALU_CMD_ADD : begin
            ialu_res    = sum1_res[`SCR1_XLEN-1:0];
        end
        SCR1_IALU_CMD_SUB : begin
            ialu_res    = sum1_res[`SCR1_XLEN-1:0];
        end
        SCR1_IALU_CMD_SUB_LT : begin
            ialu_res    = `SCR1_XLEN'(sum1_flags.s ^ sum1_flags.o);
            ialu_cmp    = sum1_flags.s ^ sum1_flags.o;
        end
        SCR1_IALU_CMD_SUB_LTU : begin
            ialu_res    = `SCR1_XLEN'(sum1_flags.c);
            ialu_cmp    = sum1_flags.c;
        end
        SCR1_IALU_CMD_SUB_EQ : begin
            ialu_res    = `SCR1_XLEN'(sum1_flags.z);
            ialu_cmp    = sum1_flags.z;
        end
        SCR1_IALU_CMD_SUB_NE : begin
            ialu_res    = `SCR1_XLEN'(~sum1_flags.z);
            ialu_cmp    = ~sum1_flags.z;
        end
        SCR1_IALU_CMD_SUB_GE : begin
            ialu_res    = `SCR1_XLEN'(~(sum1_flags.s ^ sum1_flags.o));
            ialu_cmp    = ~(sum1_flags.s ^ sum1_flags.o);
        end
        SCR1_IALU_CMD_SUB_GEU : begin
            ialu_res    = `SCR1_XLEN'(~sum1_flags.c);
            ialu_cmp    = ~sum1_flags.c;
        end
        SCR1_IALU_CMD_SLL,
        SCR1_IALU_CMD_SRL,
        SCR1_IALU_CMD_SRA: begin
            shft_cmd    = {(ialu_cmd != SCR1_IALU_CMD_SLL), (ialu_cmd == SCR1_IALU_CMD_SRA)};
            ialu_res    = shft_res;
        end
`ifdef SCR1_RVM_EXT
        SCR1_IALU_CMD_MUL,
        SCR1_IALU_CMD_MULHU,
        SCR1_IALU_CMD_MULHSU,
        SCR1_IALU_CMD_MULH : begin
            mdu_cmd     = SCR1_IALU_MDU_MUL;
 `ifdef SCR1_FAST_MUL
            ialu_res     = (|mul_cmd) ? mul_res[(32*2)-1:32] : mul_res[31:0];
 `else // ~SCR1_FAST_MUL
            case (curr_state)
                SCR1_IALU_FSM_IDLE : begin
                    ialu_res     = '0;
                    ialu_rdy     = ~iter_req;
                end
                SCR1_IALU_FSM_ITER : begin
                    ialu_res     = (|mul_cmd) ? res32_1 : res32_2;
                    ialu_rdy     = iter_rdy;
                end
            endcase
 `endif // ~SCR1_FAST_MUL
        end
        SCR1_IALU_CMD_DIV,
        SCR1_IALU_CMD_DIVU,
        SCR1_IALU_CMD_REM,
        SCR1_IALU_CMD_REMU : begin
            mdu_cmd     = SCR1_IALU_MDU_DIV;
            case (curr_state)
                SCR1_IALU_FSM_IDLE : begin
                    ialu_res     = (|ialu_op2 | div_cmd[1]) ? ialu_op1 : '1;
                    ialu_rdy     = ~iter_req;
                end
                SCR1_IALU_FSM_ITER : begin
                    ialu_res     = (div_cmd[1]) ? res32_1 : res32_2;
                    ialu_rdy     = iter_rdy & ~corr_req;
                end
                SCR1_IALU_FSM_CORR : begin
                    ialu_res     = (div_cmd[1]) ? sum2_res[31:0] : sum1_res[31:0];
                    ialu_rdy     = 1'b1;
                end
            endcase
        end
`endif // SCR1_RVM_EXT
        default : begin end
    endcase
end


`ifdef SCR1_RVM_EXT
//-------------------------------------------------------------------------------
// Save iteration state
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (ialu_vd & ~ialu_rdy) begin
        case (mdu_cmd)
            SCR1_IALU_MDU_DIV : begin
                cnt_res_reg     <= cnt_res;                     // Counter
                res32_1_c_reg   <= res32_1_c;                   // Iteration reminder carry
                res32_1_reg     <= res32_1;                     // Iteration reminder
                res32_2_reg     <= res32_2;                     // Iteration quotient
                res32_3_reg     <= res32_3;                     // Iteration reminder (low)
            end
 `ifndef SCR1_FAST_MUL
            SCR1_IALU_MDU_MUL : begin
                cnt_res_reg     <= cnt_res;                     // Counter
                res32_2_reg     <= res32_2;                     // Multiplication low result / operand 2
                res32_1_reg     <= res32_1;                     // Multiplication hight result
            end
 `endif // SCR1_FAST_MUL
            default : begin end
        endcase
    end
end
`endif // SCR1_RVM_EXT


`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT

// X checks

SCR1_SVA_IALU_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({ialu_vd, curr_state})
    ) else $error("IALU Error: unknown values");

SCR1_SVA_IALU_XCHECK_QUEUE : assert property (
    @(negedge clk) disable iff (~rst_n)
    ialu_vd |-> !$isunknown({ialu_op1, ialu_op2, ialu_cmd})
    ) else $error("IALU Error: unknown values in queue");

// Behavior checks

SCR1_SVA_IALU_ILL_STATE : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({~ialu_vd, (curr_state == SCR1_IALU_FSM_ITER), (curr_state == SCR1_IALU_FSM_CORR)})
    ) else $error("IALU Error: illegal state");

SCR1_SVA_IALU_JUMP_FROM_IDLE : assert property (
    @(negedge clk) disable iff (~rst_n)
    ((curr_state == SCR1_IALU_FSM_IDLE) & (~ialu_vd | ~iter_req))
    |=> (curr_state == SCR1_IALU_FSM_IDLE)
    ) else $error("EXU Error: illegal jump from IDLE state");

SCR1_SVA_IALU_IDLE_TO_ITER : assert property (
    @(negedge clk) disable iff (~rst_n)
    ((curr_state == SCR1_IALU_FSM_IDLE) & ialu_vd & iter_req)
    |=> (curr_state == SCR1_IALU_FSM_ITER)
    ) else $error("EXU Error: illegal change state form IDLE to ITER");

SCR1_SVA_IALU_JUMP_FROM_ITER : assert property (
    @(negedge clk) disable iff (~rst_n)
    ((curr_state == SCR1_IALU_FSM_ITER) & ~iter_rdy)
    |=> (curr_state == SCR1_IALU_FSM_ITER)
    ) else $error("EXU Error: illegal jump from ITER state");

SCR1_SVA_IALU_ITER_TO_IDLE : assert property (
    @(negedge clk) disable iff (~rst_n)
    ((curr_state == SCR1_IALU_FSM_ITER) & iter_rdy & ~corr_req)
    |=> (curr_state == SCR1_IALU_FSM_IDLE)
    ) else $error("EXU Error: illegal state change ITER to IDLE");

SCR1_SVA_IALU_ITER_TO_CORR : assert property (
    @(negedge clk) disable iff (~rst_n)
    ((curr_state == SCR1_IALU_FSM_ITER) & iter_rdy & corr_req)
    |=> ((curr_state == SCR1_IALU_FSM_CORR) ##1 (curr_state == SCR1_IALU_FSM_IDLE))
    ) else $error("EXU Error: illegal state change ITER to CORR");

`endif // SCR1_RVM_EXT

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_ialu

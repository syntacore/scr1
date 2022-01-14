/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_pipe_ialu.sv>
/// @brief      Integer Arithmetic Logic Unit (IALU)
///

//-------------------------------------------------------------------------------
 //
 // Functionality:
 // - Performs addition/subtraction and arithmetic and branch comparisons
 // - Performs logical operations (AND(I), OR(I), XOR(I))
 // - Performs address calculation for branch, jump, DMEM load and store and AUIPC
 //   instructions
 // - Performs shift operations
 // - Performs MUL/DIV operations
 //
 // Structure:
 // - Main adder
 // - Address adder
 // - Shift logic
 // - MUL/DIV logic
 // - Output result multiplexer
 //
//-------------------------------------------------------------------------------

`include "scr1_arch_description.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_search_ms1.svh"


module scr1_pipe_ialu (
`ifdef SCR1_RVM_EXT
    // Common
    input   logic                           clk,                        // IALU clock
    input   logic                           rst_n,                      // IALU reset
    input   logic                           exu2ialu_rvm_cmd_vd_i,      // MUL/DIV command valid
    output  logic                           ialu2exu_rvm_res_rdy_o,     // MUL/DIV result ready
`endif // SCR1_RVM_EXT

    // Main adder
    input   logic [`SCR1_XLEN-1:0]          exu2ialu_main_op1_i,        // main ALU 1st operand
    input   logic [`SCR1_XLEN-1:0]          exu2ialu_main_op2_i,        // main ALU 2nd operand
    input   type_scr1_ialu_cmd_sel_e        exu2ialu_cmd_i,             // IALU command
    output  logic [`SCR1_XLEN-1:0]          ialu2exu_main_res_o,        // main ALU result
    output  logic                           ialu2exu_cmp_res_o,         // IALU comparison result

    // Address adder
    input   logic [`SCR1_XLEN-1:0]          exu2ialu_addr_op1_i,        // Address adder 1st operand
    input   logic [`SCR1_XLEN-1:0]          exu2ialu_addr_op2_i,        // Address adder 2nd operand
    output  logic [`SCR1_XLEN-1:0]          ialu2exu_addr_res_o         // Address adder result
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT
 `ifdef SCR1_FAST_MUL
localparam SCR1_MUL_WIDTH     = `SCR1_XLEN;
localparam SCR1_MUL_RES_WIDTH = 2 * `SCR1_XLEN;
localparam SCR1_MDU_SUM_WIDTH = `SCR1_XLEN + 1;
 `else
localparam SCR1_MUL_STG_NUM   = 32;
localparam SCR1_MUL_WIDTH     = 32 / SCR1_MUL_STG_NUM;
localparam SCR1_MUL_CNT_INIT  = 32'b1 << (`SCR1_XLEN/SCR1_MUL_WIDTH - 2);
localparam SCR1_MDU_SUM_WIDTH = `SCR1_XLEN + SCR1_MUL_WIDTH;
 `endif // ~SCR1_FAST_MUL
localparam SCR1_DIV_WIDTH     = 1;
localparam SCR1_DIV_CNT_INIT  = 32'b1 << (`SCR1_XLEN/SCR1_DIV_WIDTH - 2);
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
    SCR1_IALU_MDU_FSM_IDLE,
    SCR1_IALU_MDU_FSM_ITER,
    SCR1_IALU_MDU_FSM_CORR
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

// Main adder signals
logic        [`SCR1_XLEN:0]                 main_sum_res;       // Main adder result
type_scr1_ialu_flags_s                      main_sum_flags;     // Main adder flags
logic                                       main_sum_pos_ovflw; // Main adder positive overflow
logic                                       main_sum_neg_ovflw; // Main adder negative overflow
logic                                       main_ops_diff_sgn;  // Main adder operands have different signs
logic                                       main_ops_non_zero;  // Both main adder operands are NOT 0

// Shifter signals
logic                                       ialu_cmd_shft;      // IALU command is shift
logic signed [`SCR1_XLEN-1:0]               shft_op1;           // SHIFT operand 1
logic        [4:0]                          shft_op2;           // SHIFT operand 2
logic        [1:0]                          shft_cmd;           // SHIFT command: 00 - logical left, 10 - logical right, 11 - arithmetical right
logic        [`SCR1_XLEN-1:0]               shft_res;           // SHIFT result

// MUL/DIV signals
`ifdef SCR1_RVM_EXT
// MUL/DIV FSM control signals
logic                                       mdu_cmd_is_iter;    // MDU Command is iterative
logic                                       mdu_iter_req;       // Request iterative stage
logic                                       mdu_iter_rdy;       // Iteration is ready
logic                                       mdu_corr_req;       // DIV/REM(U) correction request
logic                                       div_corr_req;       // Correction request for DIV operation
logic                                       rem_corr_req;       // Correction request for REM(U) operations

// MUL/DIV FSM signals
type_scr1_ialu_fsm_state                    mdu_fsm_ff;         // Current FSM state
type_scr1_ialu_fsm_state                    mdu_fsm_next;       // Next FSM state
logic                                       mdu_fsm_idle;       // MDU FSM is in IDLE state
`ifdef SCR1_TRGT_SIMULATION
logic                                       mdu_fsm_iter;       // MDU FSM is in ITER state
`endif // SCR1_TRGT_SIMULATION
logic                                       mdu_fsm_corr;       // MDU FSM is in CORR state

// MDU command signals
type_scr1_ialu_mdu_cmd                      mdu_cmd;            // MDU command: 00 - NONE, 01 - MUL,  10 - DIV
logic                                       mdu_cmd_mul;        // MDU command is MUL(HSU)
logic                                       mdu_cmd_div;        // MDU command is DIV(U)/REM(U)
logic        [1:0]                          mul_cmd;            // MUL command: 00 - MUL,  01 - MULH, 10 - MULHSU, 11 - MULHU
logic                                       mul_cmd_hi;         // High part of MUL result is requested
logic        [1:0]                          div_cmd;            // DIV command: 00 - DIV,  01 - DIVU, 10 - REM,    11 - REMU
logic                                       div_cmd_div;        // DIV command is DIV
logic                                       div_cmd_rem;        // DIV command is REM(U)

// Multiplier signals
logic                                       mul_op1_is_sgn;     // First MUL operand is signed
logic                                       mul_op2_is_sgn;     // Second MUL operand is signed
logic                                       mul_op1_sgn;        // First MUL operand is negative
logic                                       mul_op2_sgn;        // Second MUL operand is negative
logic signed [`SCR1_XLEN:0]                 mul_op1;            // MUL operand 1
logic signed [SCR1_MUL_WIDTH:0]             mul_op2;            // MUL operand 1
 `ifdef SCR1_FAST_MUL
logic signed [SCR1_MUL_RES_WIDTH-1:0]       mul_res;            // MUL result
 `else // ~SCR1_FAST_MUL
logic signed [SCR1_MDU_SUM_WIDTH:0]         mul_part_prod;
logic        [`SCR1_XLEN-1:0]               mul_res_hi;
logic        [`SCR1_XLEN-1:0]               mul_res_lo;
 `endif // ~SCR1_FAST_MUL

// Divisor signals
logic                                       div_ops_are_sgn;
logic                                       div_op1_is_neg;
logic                                       div_op2_is_neg;
logic                                       div_res_rem_c;
logic        [`SCR1_XLEN-1:0]               div_res_rem;
logic        [`SCR1_XLEN-1:0]               div_res_quo;
logic                                       div_quo_bit;
logic                                       div_dvdnd_lo_upd;
logic        [`SCR1_XLEN-1:0]               div_dvdnd_lo_ff;
logic        [`SCR1_XLEN-1:0]               div_dvdnd_lo_next;

// MDU adder signals
logic                                       mdu_sum_sub;        // MDU adder operation: 0 - add, 1 - sub
logic signed [SCR1_MDU_SUM_WIDTH-1:0]       mdu_sum_op1;        // MDU adder operand 1
logic signed [SCR1_MDU_SUM_WIDTH-1:0]       mdu_sum_op2;        // MDU adder operand 2
logic signed [SCR1_MDU_SUM_WIDTH-1:0]       mdu_sum_res;        // MDU adder result

// MDU iteration counter signals
logic                                       mdu_iter_cnt_en;
logic        [`SCR1_XLEN-1:0]               mdu_iter_cnt;
logic        [`SCR1_XLEN-1:0]               mdu_iter_cnt_next;

// Intermediate results registers
logic                                       mdu_res_upd;
logic                                       mdu_res_c_ff;
logic                                       mdu_res_c_next;
logic        [`SCR1_XLEN-1:0]               mdu_res_hi_ff;
logic        [`SCR1_XLEN-1:0]               mdu_res_hi_next;
logic        [`SCR1_XLEN-1:0]               mdu_res_lo_ff;
logic        [`SCR1_XLEN-1:0]               mdu_res_lo_next;
`endif // SCR1_RVM_EXT

//-------------------------------------------------------------------------------
// Main adder
//-------------------------------------------------------------------------------
//
 // Main adder is used for the following types of operations:
 // - Addition/subtraction          (ADD/ADDI/SUB)
 // - Branch comparisons            (BEQ/BNE/BLT(U)/BGE(U))
 // - Arithmetic comparisons        (SLT(U)/SLTI(U))
//

// Carry out (MSB of main_sum_res) is evaluated correctly because the result
// width equals to the maximum width of both the right-hand and left-hand side variables
always_comb begin
    main_sum_res = (exu2ialu_cmd_i != SCR1_IALU_CMD_ADD)
                 ? ({1'b0, exu2ialu_main_op1_i} - {1'b0, exu2ialu_main_op2_i})   // Subtraction and comparison
                 : ({1'b0, exu2ialu_main_op1_i} + {1'b0, exu2ialu_main_op2_i});  // Addition

    main_sum_pos_ovflw = ~exu2ialu_main_op1_i[`SCR1_XLEN-1]
                       &  exu2ialu_main_op2_i[`SCR1_XLEN-1]
                       &  main_sum_res[`SCR1_XLEN-1];
    main_sum_neg_ovflw =  exu2ialu_main_op1_i[`SCR1_XLEN-1]
                       & ~exu2ialu_main_op2_i[`SCR1_XLEN-1]
                       & ~main_sum_res[`SCR1_XLEN-1];

    // FLAGS1 - flags for comparison (result of subtraction)
    main_sum_flags.c = main_sum_res[`SCR1_XLEN];
    main_sum_flags.z = ~|main_sum_res[`SCR1_XLEN-1:0];
    main_sum_flags.s = main_sum_res[`SCR1_XLEN-1];
    main_sum_flags.o = main_sum_pos_ovflw | main_sum_neg_ovflw;
end

//-------------------------------------------------------------------------------
// Address adder
//-------------------------------------------------------------------------------
//
 // Additional adder is used for the following types of operations:
 // - PC-based address calculation          (AUIPC)
 // - IMEM branch address calculation       (BEQ/BNE/BLT(U)/BGE(U))
 // - IMEM jump address calculation         (JAL/JALR)
 // - DMEM load address calculation         (LB(U)/LH(U)/LW)
 // - DMEM store address calculation        (SB/SH/SW)
//

assign ialu2exu_addr_res_o = exu2ialu_addr_op1_i + exu2ialu_addr_op2_i;

//-------------------------------------------------------------------------------
// Shift logic
//-------------------------------------------------------------------------------
 //
 // Shift logic supports the following types of shift operations:
 // - Logical left shift      (SLLI/SLL)
 // - Logical right shift     (SRLI/SRL)
 // - Arithmetic right shift  (SRAI/SRA)
//

assign ialu_cmd_shft = (exu2ialu_cmd_i == SCR1_IALU_CMD_SLL)
                     | (exu2ialu_cmd_i == SCR1_IALU_CMD_SRL)
                     | (exu2ialu_cmd_i == SCR1_IALU_CMD_SRA);
assign shft_cmd      = ialu_cmd_shft
                     ? {(exu2ialu_cmd_i != SCR1_IALU_CMD_SLL),
                        (exu2ialu_cmd_i == SCR1_IALU_CMD_SRA)}
                     : 2'b00;

always_comb begin
    shft_op1 = exu2ialu_main_op1_i;
    shft_op2 = exu2ialu_main_op2_i[4:0];
    case (shft_cmd)
        2'b10   : shft_res = shft_op1  >> shft_op2;
        2'b11   : shft_res = shft_op1 >>> shft_op2;
        default : shft_res = shft_op1  << shft_op2;
    endcase
end

`ifdef SCR1_RVM_EXT
//-------------------------------------------------------------------------------
// MUL/DIV logic
//-------------------------------------------------------------------------------
//
 // MUL/DIV instructions use the following functional units:
 // - MUL/DIV FSM control logic, including iteration number counter
 // - MUL/DIV FSM
 // - MUL logic
 // - DIV logic
 // - MDU adder to produce an intermediate result
 // - 2 registers to save the intermediate result (shared between MUL and DIV
 //   operations)
//

//-------------------------------------------------------------------------------
// MUL/DIV FSM Control logic
//-------------------------------------------------------------------------------

assign mdu_cmd_div = (exu2ialu_cmd_i == SCR1_IALU_CMD_DIV)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_DIVU)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_REM)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_REMU);
assign mdu_cmd_mul = (exu2ialu_cmd_i == SCR1_IALU_CMD_MUL)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_MULH)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_MULHU)
                   | (exu2ialu_cmd_i == SCR1_IALU_CMD_MULHSU);

assign mdu_cmd     = mdu_cmd_div ? SCR1_IALU_MDU_DIV
                   : mdu_cmd_mul ? SCR1_IALU_MDU_MUL
                                 : SCR1_IALU_MDU_NONE;

assign main_ops_non_zero = |exu2ialu_main_op1_i & |exu2ialu_main_op2_i;
assign main_ops_diff_sgn = exu2ialu_main_op1_i[`SCR1_XLEN-1]
                         ^ exu2ialu_main_op2_i[`SCR1_XLEN-1];

 `ifdef SCR1_FAST_MUL
    assign mdu_cmd_is_iter = mdu_cmd_div;
 `else // ~SCR1_FAST_MUL
    assign mdu_cmd_is_iter = mdu_cmd_mul | mdu_cmd_div;
 `endif // ~SCR1_FAST_MUL

assign mdu_iter_req = mdu_cmd_is_iter ? (main_ops_non_zero & mdu_fsm_idle) : 1'b0;
assign mdu_iter_rdy = mdu_iter_cnt[0];

assign div_cmd_div = (div_cmd == 2'b00);
assign div_cmd_rem = div_cmd[1];

// Correction request signals
assign div_corr_req = div_cmd_div & main_ops_diff_sgn;
assign rem_corr_req = div_cmd_rem & |div_res_rem & (div_op1_is_neg ^ div_res_rem_c);
assign mdu_corr_req = mdu_cmd_div & (div_corr_req | rem_corr_req);

// MDU iteration counter
//------------------------------------------------------------------------------

assign mdu_iter_cnt_en = exu2ialu_rvm_cmd_vd_i & ~ialu2exu_rvm_res_rdy_o;

always_ff @(posedge clk) begin
    if (mdu_iter_cnt_en) begin
        mdu_iter_cnt <= mdu_iter_cnt_next;
    end
end

assign mdu_iter_cnt_next = ~mdu_fsm_idle ? mdu_iter_cnt >> 1
                         : mdu_cmd_div   ? SCR1_DIV_CNT_INIT
 `ifndef SCR1_FAST_MUL
                         : mdu_cmd_mul   ? SCR1_MUL_CNT_INIT
 `endif // ~SCR1_FAST_MUL
                                         : mdu_iter_cnt;

//-------------------------------------------------------------------------------
// MUL/DIV FSM
//-------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mdu_fsm_ff <= SCR1_IALU_MDU_FSM_IDLE;
    end else begin
        mdu_fsm_ff <= mdu_fsm_next;
    end
end

always_comb begin
    mdu_fsm_next = SCR1_IALU_MDU_FSM_IDLE;

    if (exu2ialu_rvm_cmd_vd_i) begin
        case (mdu_fsm_ff)
            SCR1_IALU_MDU_FSM_IDLE : begin
                mdu_fsm_next = mdu_iter_req  ? SCR1_IALU_MDU_FSM_ITER
                                             : SCR1_IALU_MDU_FSM_IDLE;
            end
            SCR1_IALU_MDU_FSM_ITER : begin
                mdu_fsm_next = ~mdu_iter_rdy ? SCR1_IALU_MDU_FSM_ITER
                             : mdu_corr_req  ? SCR1_IALU_MDU_FSM_CORR
                                             : SCR1_IALU_MDU_FSM_IDLE;
            end
            SCR1_IALU_MDU_FSM_CORR : begin
                mdu_fsm_next = SCR1_IALU_MDU_FSM_IDLE;
            end
        endcase
    end
end

assign mdu_fsm_idle = (mdu_fsm_ff == SCR1_IALU_MDU_FSM_IDLE);
`ifdef SCR1_TRGT_SIMULATION
assign mdu_fsm_iter = (mdu_fsm_ff == SCR1_IALU_MDU_FSM_ITER);
`endif // SCR1_TRGT_SIMULATION
assign mdu_fsm_corr = (mdu_fsm_ff == SCR1_IALU_MDU_FSM_CORR);

//-------------------------------------------------------------------------------
// Multiplier logic
//-------------------------------------------------------------------------------
//
 // Multiplication has 2 options: fast (1 cycle) and Radix-2 (32 cycles) multiplication.
 //
 // 1. Fast multiplication uses the straightforward approach when 2 operands are
 // multiplied in one cycle
 //
 // 2. Radix-2 multiplication uses 2 registers (high and low part of multiplication)
 //
 // Radix-2 algorithm:
 // 1. Initialize registers
 // 2. Create a partial product by multiplying multiplicand by the LSB of multiplier
 // 3. Add the partial product to the previous (intermediate) value of multiplication
 //    result (stored into high and low parts of multiplication result register)
 // 4. Shift the low part of multiplication result register right
 // 4. Store the addition result into the high part of multiplication result register
 // 6. If iteration is not ready, go to step 2. Otherwise multiplication is done
 //
//

assign mul_cmd  = {((exu2ialu_cmd_i == SCR1_IALU_CMD_MULHU) | (exu2ialu_cmd_i == SCR1_IALU_CMD_MULHSU)),
                   ((exu2ialu_cmd_i == SCR1_IALU_CMD_MULHU) | (exu2ialu_cmd_i == SCR1_IALU_CMD_MULH))};

assign mul_cmd_hi     = |mul_cmd;
assign mul_op1_is_sgn = ~&mul_cmd;
assign mul_op2_is_sgn = ~mul_cmd[1];
assign mul_op1_sgn    = mul_op1_is_sgn & exu2ialu_main_op1_i[`SCR1_XLEN-1];
assign mul_op2_sgn    = mul_op2_is_sgn & exu2ialu_main_op2_i[`SCR1_XLEN-1];

`ifdef SCR1_FAST_MUL
assign mul_op1 = mdu_cmd_mul ? $signed({mul_op1_sgn, exu2ialu_main_op1_i}) : '0;
assign mul_op2 = mdu_cmd_mul ? $signed({mul_op2_sgn, exu2ialu_main_op2_i}) : '0;
assign mul_res = mdu_cmd_mul ? mul_op1 * mul_op2                           : $signed('0);
`else // ~SCR1_FAST_MUL
assign mul_op1 = mdu_cmd_mul  ? $signed({mul_op1_sgn, exu2ialu_main_op1_i}) : '0;
assign mul_op2 = ~mdu_cmd_mul ? '0
               : mdu_fsm_idle ? $signed({1'b0, exu2ialu_main_op2_i[SCR1_MUL_WIDTH-1:0]})
                              : $signed({(mdu_iter_cnt[0] & mul_op2_is_sgn & mdu_res_lo_ff[SCR1_MUL_WIDTH-1]),
                                          mdu_res_lo_ff[SCR1_MUL_WIDTH-1:0]});

assign mul_part_prod            = mdu_cmd_mul  ? mul_op1 * mul_op2 : $signed('0);
assign {mul_res_hi, mul_res_lo} = ~mdu_cmd_mul ? '0
                                : mdu_fsm_idle ? ({mdu_sum_res, exu2ialu_main_op2_i[`SCR1_XLEN-1:SCR1_MUL_WIDTH]})
                                               : ({mdu_sum_res, mdu_res_lo_ff[`SCR1_XLEN-1:SCR1_MUL_WIDTH]});
`endif // ~SCR1_FAST_MUL

//-------------------------------------------------------------------------------
// Divider logic
//-------------------------------------------------------------------------------
//
 // Division uses a non-restoring algorithm. 3 registers are used:
 // - Remainder register
 // - Quotient register
 // - Dividend low part register (for corner case quotient bit calculation)
 //
 // Algorithm:
 // 1. Initialize registers
 // 2. Shift remainder and dividend low part registers left
 // 3. Compare remainder register with the divisor (taking previous quotient bit
 //    and operands signs into account) and calculate quotient bit based on the
 //    comparison results
 // 4. Shift quotient register left, append quotient bit to the quotient register
 // 5. If iteration is not ready, go to step 2. Otherwise go to step 6
 // 6. Do correction if necessary, otherwise division is done
 //
 // Quotient bit calculation has a corner case:
 // When dividend is negative result carry bit check takes into account only
 // the case of remainder register been greater than divisor. To handle
 // equality case we should check if both the comparison result and the
 // lower part of dividend are zero
//

assign div_cmd  = {((exu2ialu_cmd_i == SCR1_IALU_CMD_REM)   | (exu2ialu_cmd_i == SCR1_IALU_CMD_REMU)),
                   ((exu2ialu_cmd_i == SCR1_IALU_CMD_REMU)  | (exu2ialu_cmd_i == SCR1_IALU_CMD_DIVU))};

assign div_ops_are_sgn = ~div_cmd[0];
assign div_op1_is_neg  = div_ops_are_sgn & exu2ialu_main_op1_i[`SCR1_XLEN-1];
assign div_op2_is_neg  = div_ops_are_sgn & exu2ialu_main_op2_i[`SCR1_XLEN-1];

always_comb begin
    div_res_rem_c = '0;
    div_res_rem   = '0;
    div_res_quo   = '0;
    div_quo_bit   = 1'b0;
    if (mdu_cmd_div & ~mdu_fsm_corr) begin
        div_res_rem_c = mdu_sum_res[SCR1_MDU_SUM_WIDTH-1];
        div_res_rem   = mdu_sum_res[SCR1_MDU_SUM_WIDTH-2:0];
        div_quo_bit   = ~(div_op1_is_neg ^ div_res_rem_c)
                      | (div_op1_is_neg & ({mdu_sum_res, div_dvdnd_lo_next} == '0));
        div_res_quo   = mdu_fsm_idle
                      ? {'0, div_quo_bit}
                      : {mdu_res_lo_ff[`SCR1_XLEN-2:0], div_quo_bit};
    end
end

// Dividend low part register
//------------------------------------------------------------------------------

assign div_dvdnd_lo_upd = exu2ialu_rvm_cmd_vd_i & ~ialu2exu_rvm_res_rdy_o;

always_ff @(posedge clk) begin
    if (div_dvdnd_lo_upd) begin
        div_dvdnd_lo_ff <= div_dvdnd_lo_next;
    end
end

assign div_dvdnd_lo_next = (~mdu_cmd_div | mdu_fsm_corr) ? '0
                         : mdu_fsm_idle                  ? exu2ialu_main_op1_i << 1
                                                         : div_dvdnd_lo_ff     << 1;

//-------------------------------------------------------------------------------
// MDU adder
//-------------------------------------------------------------------------------

always_comb begin
    mdu_sum_sub    = 1'b0;
    mdu_sum_op1    = '0;
    mdu_sum_op2    = '0;
    case (mdu_cmd)
        SCR1_IALU_MDU_DIV : begin
            logic           sgn;
            logic           inv;

            sgn         = mdu_fsm_corr ? div_op1_is_neg ^ mdu_res_c_ff
                        : mdu_fsm_idle ? 1'b0
                                       : ~mdu_res_lo_ff[0];
            inv         = div_ops_are_sgn & main_ops_diff_sgn;
            mdu_sum_sub = ~inv ^ sgn;
            mdu_sum_op1 = mdu_fsm_corr ? $signed({1'b0, mdu_res_hi_ff})
                        : mdu_fsm_idle ? $signed({div_op1_is_neg, exu2ialu_main_op1_i[`SCR1_XLEN-1]})
                                       : $signed({mdu_res_hi_ff, div_dvdnd_lo_ff[`SCR1_XLEN-1]});
            mdu_sum_op2 = $signed({div_op2_is_neg, exu2ialu_main_op2_i});
        end
`ifndef SCR1_FAST_MUL
        SCR1_IALU_MDU_MUL : begin
            mdu_sum_op1 = mdu_fsm_idle
                        ? '0
                        : $signed({(mul_op1_is_sgn & mdu_res_hi_ff[`SCR1_XLEN-1]), mdu_res_hi_ff});
            mdu_sum_op2 = mul_part_prod;
        end
`endif // SCR1_FAST_MUL
        default : begin end
    endcase
    mdu_sum_res = mdu_sum_sub
                ? (mdu_sum_op1 - mdu_sum_op2)
                : (mdu_sum_op1 + mdu_sum_op2);
end

//-------------------------------------------------------------------------------
// MUL/DIV intermediate results registers
//-------------------------------------------------------------------------------

assign mdu_res_upd = exu2ialu_rvm_cmd_vd_i & ~ialu2exu_rvm_res_rdy_o;

always_ff @(posedge clk) begin
    if (mdu_res_upd) begin
        mdu_res_c_ff  <= mdu_res_c_next;
        mdu_res_hi_ff <= mdu_res_hi_next;
        mdu_res_lo_ff <= mdu_res_lo_next;
    end
end

assign mdu_res_c_next  = mdu_cmd_div ? div_res_rem_c : mdu_res_c_ff;
assign mdu_res_hi_next = mdu_cmd_div ? div_res_rem
 `ifndef SCR1_FAST_MUL
                       : mdu_cmd_mul ? mul_res_hi
 `endif // SCR1_FAST_MUL
                                     : mdu_res_hi_ff;
assign mdu_res_lo_next = mdu_cmd_div ? div_res_quo
 `ifndef SCR1_FAST_MUL
                       : mdu_cmd_mul ? mul_res_lo
 `endif // SCR1_FAST_MUL
                                     : mdu_res_lo_ff;
`endif // SCR1_RVM_EXT

//-------------------------------------------------------------------------------
// Operation result forming
//-------------------------------------------------------------------------------

always_comb begin
    ialu2exu_main_res_o    = '0;
    ialu2exu_cmp_res_o     = 1'b0;
`ifdef SCR1_RVM_EXT
    ialu2exu_rvm_res_rdy_o = 1'b1;
`endif // SCR1_RVM_EXT

    case (exu2ialu_cmd_i)
        SCR1_IALU_CMD_AND : begin
            ialu2exu_main_res_o = exu2ialu_main_op1_i & exu2ialu_main_op2_i;
        end
        SCR1_IALU_CMD_OR : begin
            ialu2exu_main_res_o = exu2ialu_main_op1_i | exu2ialu_main_op2_i;
        end
        SCR1_IALU_CMD_XOR : begin
            ialu2exu_main_res_o = exu2ialu_main_op1_i ^ exu2ialu_main_op2_i;
        end
        SCR1_IALU_CMD_ADD : begin
            ialu2exu_main_res_o = main_sum_res[`SCR1_XLEN-1:0];
        end
        SCR1_IALU_CMD_SUB : begin
            ialu2exu_main_res_o = main_sum_res[`SCR1_XLEN-1:0];
        end
        SCR1_IALU_CMD_SUB_LT : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(main_sum_flags.s ^ main_sum_flags.o);
            ialu2exu_cmp_res_o  = main_sum_flags.s ^ main_sum_flags.o;
        end
        SCR1_IALU_CMD_SUB_LTU : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(main_sum_flags.c);
            ialu2exu_cmp_res_o  = main_sum_flags.c;
        end
        SCR1_IALU_CMD_SUB_EQ : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(main_sum_flags.z);
            ialu2exu_cmp_res_o  = main_sum_flags.z;
        end
        SCR1_IALU_CMD_SUB_NE : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(~main_sum_flags.z);
            ialu2exu_cmp_res_o  = ~main_sum_flags.z;
        end
        SCR1_IALU_CMD_SUB_GE : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(~(main_sum_flags.s ^ main_sum_flags.o));
            ialu2exu_cmp_res_o  = ~(main_sum_flags.s ^ main_sum_flags.o);
        end
        SCR1_IALU_CMD_SUB_GEU : begin
            ialu2exu_main_res_o = `SCR1_XLEN'(~main_sum_flags.c);
            ialu2exu_cmp_res_o  = ~main_sum_flags.c;
        end
        SCR1_IALU_CMD_SLL,
        SCR1_IALU_CMD_SRL,
        SCR1_IALU_CMD_SRA: begin
            ialu2exu_main_res_o = shft_res;
        end
`ifdef SCR1_RVM_EXT
        SCR1_IALU_CMD_MUL,
        SCR1_IALU_CMD_MULHU,
        SCR1_IALU_CMD_MULHSU,
        SCR1_IALU_CMD_MULH : begin
 `ifdef SCR1_FAST_MUL
            ialu2exu_main_res_o = mul_cmd_hi
                                ? mul_res[SCR1_MUL_RES_WIDTH-1:`SCR1_XLEN]
                                : mul_res[`SCR1_XLEN-1:0];
 `else // ~SCR1_FAST_MUL
            case (mdu_fsm_ff)
                SCR1_IALU_MDU_FSM_IDLE : begin
                    ialu2exu_main_res_o    = '0;
                    ialu2exu_rvm_res_rdy_o = ~mdu_iter_req;
                end
                SCR1_IALU_MDU_FSM_ITER : begin
                    ialu2exu_main_res_o    = mul_cmd_hi ? mul_res_hi : mul_res_lo;
                    ialu2exu_rvm_res_rdy_o = mdu_iter_rdy;
                end
            endcase
 `endif // ~SCR1_FAST_MUL
        end
        SCR1_IALU_CMD_DIV,
        SCR1_IALU_CMD_DIVU,
        SCR1_IALU_CMD_REM,
        SCR1_IALU_CMD_REMU : begin
            case (mdu_fsm_ff)
                SCR1_IALU_MDU_FSM_IDLE : begin
                    ialu2exu_main_res_o    = (|exu2ialu_main_op2_i | div_cmd_rem)
                                           ? exu2ialu_main_op1_i
                                           : '1;
                    ialu2exu_rvm_res_rdy_o = ~mdu_iter_req;
                end
                SCR1_IALU_MDU_FSM_ITER : begin
                    ialu2exu_main_res_o    = div_cmd_rem ? div_res_rem : div_res_quo;
                    ialu2exu_rvm_res_rdy_o = mdu_iter_rdy & ~mdu_corr_req;
                end
                SCR1_IALU_MDU_FSM_CORR : begin
                    ialu2exu_main_res_o    = div_cmd_rem
                                           ? mdu_sum_res[`SCR1_XLEN-1:0]
                                           : -mdu_res_lo_ff[`SCR1_XLEN-1:0];
                    ialu2exu_rvm_res_rdy_o = 1'b1;
                end
            endcase
        end
`endif // SCR1_RVM_EXT
        default : begin end
    endcase
end


`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

`ifdef SCR1_RVM_EXT

// X checks

SCR1_SVA_IALU_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2ialu_rvm_cmd_vd_i, mdu_fsm_ff})
    ) else $error("IALU Error: unknown values");

SCR1_SVA_IALU_XCHECK_QUEUE : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2ialu_rvm_cmd_vd_i |->
    !$isunknown({exu2ialu_main_op1_i, exu2ialu_main_op2_i, exu2ialu_cmd_i})
    ) else $error("IALU Error: unknown values in queue");

// Behavior checks

SCR1_SVA_IALU_ILL_STATE : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({~exu2ialu_rvm_cmd_vd_i, mdu_fsm_iter, mdu_fsm_corr})
    ) else $error("IALU Error: illegal state");

SCR1_SVA_IALU_JUMP_FROM_IDLE : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mdu_fsm_idle & (~exu2ialu_rvm_cmd_vd_i | ~mdu_iter_req)) |=> mdu_fsm_idle
    ) else $error("EXU Error: illegal jump from IDLE state");

SCR1_SVA_IALU_IDLE_TO_ITER : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mdu_fsm_idle & exu2ialu_rvm_cmd_vd_i & mdu_iter_req) |=> mdu_fsm_iter
    ) else $error("EXU Error: illegal change state form IDLE to ITER");

SCR1_SVA_IALU_JUMP_FROM_ITER : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mdu_fsm_iter & ~mdu_iter_rdy) |=> mdu_fsm_iter
    ) else $error("EXU Error: illegal jump from ITER state");

SCR1_SVA_IALU_ITER_TO_IDLE : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mdu_fsm_iter & mdu_iter_rdy & ~mdu_corr_req) |=> mdu_fsm_idle
    ) else $error("EXU Error: illegal state change ITER to IDLE");

SCR1_SVA_IALU_ITER_TO_CORR : assert property (
    @(negedge clk) disable iff (~rst_n)
    (mdu_fsm_iter & mdu_iter_rdy & mdu_corr_req) |=> mdu_fsm_corr
    ) else $error("EXU Error: illegal state change ITER to CORR");

SCR1_SVA_IALU_CORR_TO_IDLE : assert property (
    @(negedge clk) disable iff (~rst_n)
    mdu_fsm_corr |=> mdu_fsm_idle
    ) else $error("EXU Error: illegal state stay in CORR");

`endif // SCR1_RVM_EXT

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_ialu

/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_ifu.sv>
/// @brief      Instruction Fetch Unit (IFU)
///

`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

module scr1_pipe_ifu
(
    // Control signals
    input   logic                               rst_n,
    input   logic                               clk,
    // Instruction memory interface
    input   logic                               imem_req_ack,
    output  logic                               imem_req,
    output  type_scr1_mem_cmd_e                 imem_cmd,
    output  logic [`SCR1_IMEM_AWIDTH-1:0]       imem_addr,
    input   logic [`SCR1_IMEM_DWIDTH-1:0]       imem_rdata,
    input   type_scr1_mem_resp_e                imem_resp,
    // NEW_PC interface
    input   logic                               new_pc_req,         // New PC request (jumps, branches, traps etc)
    input   logic [`SCR1_XLEN-1:0]              new_pc,             // New PC
    input   logic                               stop_fetch,         // Stop IFU
`ifdef SCR1_DBGC_EN
    input   logic                               fetch_dbgc,         // Fetch instructions provided by DBGC
    input   logic [`SCR1_IMEM_DWIDTH-1:0]       dbgc_instr,
`endif // SCR1_DBGC_EN
`ifdef SCR1_CLKCTRL_EN
    output  logic                               imem_txns_pending,  // There are pending imem transactions
`endif // SCR1_CLKCTRL_EN
    // Instruction decode unit interface
    input   logic                               idu2ifu_rdy,        // IDU ready for new data
    output  logic [`SCR1_IMEM_DWIDTH-1:0]       ifu2idu_instr,      // IFU instruction
    output  logic                               ifu2idu_imem_err,   // Instruction access fault exception
    output  logic                               ifu2idu_err_rvi_hi, // 1 - imem fault when trying to fetch second half of an unaligned RVI instruction
    output  logic                               ifu2idu_vd,         // IFU request

    output  logic                               ifu_busy            // IFU busy
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------

localparam SCR1_IFU_Q_SIZE_WORD     = 2;
localparam SCR1_IFU_Q_SIZE_HALF     = SCR1_IFU_Q_SIZE_WORD * 2;
localparam SCR1_TXN_CNT_W           = 3;

localparam SCR1_IFU_QUEUE_ADR_W     = $clog2(SCR1_IFU_Q_SIZE_HALF);
localparam SCR1_IFU_QUEUE_PTR_W     = SCR1_IFU_QUEUE_ADR_W + 1;

localparam SCR1_IFU_Q_FREE_H_W      = $clog2(SCR1_IFU_Q_SIZE_HALF + 1);
localparam SCR1_IFU_Q_FREE_W_W      = $clog2(SCR1_IFU_Q_SIZE_WORD + 1);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------

typedef enum logic {
    SCR1_FSM_IDLE,
    SCR1_FSM_FETCH
} type_scr1_ifu_fsm_e;

typedef enum logic[1:0] {
    SCR1_WE_NONE,                   // No write to queue
    SCR1_WE_RDATA_FULL,             // Write 32 rdata bits to queue
    SCR1_WE_RDATA_HI                // Write 16 upper rdata bits to queue
} type_scr1_we_e;

typedef enum logic[1:0] {
    SCR1_RE_NONE,                   // No queue read
    SCR1_RE_HALFWORD,               // Read halfword
    SCR1_RE_WORD                    // Read word
} type_scr1_re_e;

typedef enum logic {
    SCR1_RVI_PART2,                 // Rdata has RVI upper 16 bits in its lower 16 bits
    SCR1_OTHER
} type_scr1_rdata_type_e;

`ifdef SCR1_IFU_QUEUE_BYPASS
typedef enum logic[1:0] {
    SCR1_BYPASS_NONE,               // No bypass
    SCR1_BYPASS_RVC,                // Bypass RVC
    SCR1_BYPASS_RVI_RDATA_QUEUE,    // Bypass RVI, rdata+queue
    SCR1_BYPASS_RVI_RDATA           // Bypass RVI, rdata only
} type_scr1_bypass_e;
`endif // SCR1_IFU_QUEUE_BYPASS

typedef enum logic [2:0] {
    // SCR1_RDATA_<UPPER_16_BITS>_<LOWER_16_BITS>
    SCR1_RDATA_NONE,                // No valid rdata
    SCR1_RDATA_RVI_HI_RVI_LO,       // Full RV32I instruction
    SCR1_RDATA_RVC_RVC,
    SCR1_RDATA_RVI_LO_RVC,
    SCR1_RDATA_RVC_RVI_HI,
    SCR1_RDATA_RVI_LO_RVI_HI,
    SCR1_RDATA_RVC_NV,              // Rdata after unaligned new_pc
    SCR1_RDATA_RVI_LO_NV            // Rdata after unaligned new_pc
} type_scr1_rdata_ident_e;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

type_scr1_ifu_fsm_e                 fsm;
logic [`SCR1_XLEN-1:2]              imem_addr_r;
logic [SCR1_TXN_CNT_W-1:0]          num_txns_pending;           // Transactions sent but not yet returned
logic [SCR1_TXN_CNT_W-1:0]          discard_resp_cnt;           // Number of imem responses to discard
logic [SCR1_TXN_CNT_W-1:0]          discard_resp_cnt_new;
logic                               discard_resp;
logic [SCR1_TXN_CNT_W-1:0]          num_vd_txns_pending;
logic                               num_txns_pending_full;
logic                               imem_resp_ok;
logic                               imem_resp_er;
logic                               imem_resp_vd;
logic                               new_pc_unaligned;

logic                               q_empty;
logic                               q_flush;
logic [SCR1_IFU_QUEUE_PTR_W-1:0]    q_rptr;
logic [SCR1_IFU_QUEUE_PTR_W-1:0]    q_rptr_next;
logic [SCR1_IFU_QUEUE_PTR_W-1:0]    q_wptr;
logic [SCR1_IFU_QUEUE_PTR_W-1:0]    q_wptr_next;
logic [SCR1_IFU_Q_FREE_H_W-1:0]     q_ocpd_h;                   // Queue occupied halfwords
logic [SCR1_IFU_Q_FREE_H_W-1:0]     q_free_h_next;
logic [SCR1_IFU_Q_FREE_W_W-1:0]     q_free_w_next;              // Used for imem_req logic

logic [`SCR1_IMEM_DWIDTH/2-1:0]     q_data  [SCR1_IFU_Q_SIZE_HALF];
logic                               q_err   [SCR1_IFU_Q_SIZE_HALF];
type_scr1_re_e                      q_re;                       // Queue read
type_scr1_we_e                      q_we;                       // Queue write
logic                               q_head_rvc;                 // RVC instruction at read pointer
logic                               q_head_rvi;                 // RVI instruction at read pointer
logic [`SCR1_IMEM_DWIDTH/2-1:0]     q_data_head;
logic [`SCR1_IMEM_DWIDTH/2-1:0]     q_data_next;
logic                               q_err_head;
logic                               q_err_next;

type_scr1_rdata_type_e              rdata_curr;
type_scr1_rdata_type_e              rdata_next;
type_scr1_rdata_ident_e             rdata_ident;                // Identifies contents of rdata
`ifdef SCR1_IFU_QUEUE_BYPASS
type_scr1_bypass_e                  instr_bypass;               // Do not write to queue, pass directly to IDU
logic                               instr_bypass_vd;
`endif // SCR1_IFU_QUEUE_BYPASS


//-------------------------------------------------------------------------------
// Instruction queue logic
//-------------------------------------------------------------------------------
assign q_empty          = (q_rptr == q_wptr);
assign q_flush          = new_pc_req | stop_fetch;

assign q_ocpd_h         = SCR1_IFU_Q_FREE_H_W'(q_wptr - q_rptr);
assign q_free_h_next    = SCR1_IFU_Q_FREE_H_W'(SCR1_IFU_Q_SIZE_HALF - (q_wptr - q_rptr_next));
assign q_free_w_next    = SCR1_IFU_Q_FREE_W_W'(q_free_h_next >> 1'b1);

assign q_head_rvi       = &(q_data_head[1:0]);
assign q_head_rvc       = ~q_head_rvi;

assign q_data_head      = q_data [SCR1_IFU_QUEUE_ADR_W'(q_rptr)];
assign q_data_next      = q_data [SCR1_IFU_QUEUE_ADR_W'(q_rptr + 1'b1)];
assign q_err_head       = q_err  [SCR1_IFU_QUEUE_ADR_W'(q_rptr)];
assign q_err_next       = q_err  [SCR1_IFU_QUEUE_ADR_W'(q_rptr + 1'b1)];


always_comb begin
    q_re = SCR1_RE_NONE;

    if (~q_empty & ifu2idu_vd & idu2ifu_rdy) begin
        if (q_head_rvc | q_err_head
`ifdef SCR1_IFU_QUEUE_BYPASS
                | (q_head_rvi & instr_bypass_vd)
`endif // SCR1_IFU_QUEUE_BYPASS
            ) begin
            q_re = SCR1_RE_HALFWORD;
        end else begin
            q_re = SCR1_RE_WORD;
        end
    end
end

always_comb begin
    q_we = SCR1_WE_NONE;

    if (~discard_resp) begin
        if (imem_resp_ok) begin
`ifdef SCR1_IFU_QUEUE_BYPASS
            case (rdata_ident)
                SCR1_RDATA_NONE             : q_we = SCR1_WE_NONE;
                SCR1_RDATA_RVI_LO_NV        : q_we = SCR1_WE_RDATA_HI;
                SCR1_RDATA_RVC_NV           : q_we = (instr_bypass_vd & idu2ifu_rdy) ? SCR1_WE_NONE : SCR1_WE_RDATA_HI;
                SCR1_RDATA_RVI_HI_RVI_LO    : q_we = (instr_bypass_vd & idu2ifu_rdy) ? SCR1_WE_NONE : SCR1_WE_RDATA_FULL;
                SCR1_RDATA_RVC_RVC,
                SCR1_RDATA_RVI_LO_RVC,
                SCR1_RDATA_RVC_RVI_HI,
                SCR1_RDATA_RVI_LO_RVI_HI    : q_we = (instr_bypass_vd & idu2ifu_rdy) ? SCR1_WE_RDATA_HI : SCR1_WE_RDATA_FULL;
            endcase // rdata_ident
`else // SCR1_IFU_QUEUE_BYPASS
            case (rdata_ident)
                SCR1_RDATA_NONE             : q_we = SCR1_WE_NONE;
                SCR1_RDATA_RVC_NV,
                SCR1_RDATA_RVI_LO_NV        : q_we = SCR1_WE_RDATA_HI;
                default                     : q_we = SCR1_WE_RDATA_FULL;
            endcase // rdata_ident
`endif // SCR1_IFU_QUEUE_BYPASS
        end else if (imem_resp_er) begin
            q_we = SCR1_WE_RDATA_FULL;
        end // imem_resp_er
    end // ~discard_resp
end

always_comb begin
    q_rptr_next = q_rptr;
    q_wptr_next = q_wptr;

    if ((q_we == SCR1_WE_RDATA_HI) | (q_we == SCR1_WE_RDATA_FULL)) begin
        q_wptr_next = q_wptr + ((q_we == SCR1_WE_RDATA_FULL) ? 2'd2 : 1'b1);
    end
    if ((q_re == SCR1_RE_WORD) | (q_re == SCR1_RE_HALFWORD)) begin
        q_rptr_next = q_rptr + ((q_re == SCR1_RE_WORD) ? 2'd2 : 1'b1);
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        q_rptr  <= '0;
        q_wptr  <= '0;
    end else begin
        if (q_flush) begin
            q_rptr  <= '0;
            q_wptr  <= '0;
        end else begin
            if ((q_we == SCR1_WE_RDATA_HI) | (q_we == SCR1_WE_RDATA_FULL)) begin
                q_wptr  <= q_wptr_next;
            end
            if ((q_re == SCR1_RE_WORD) | (q_re == SCR1_RE_HALFWORD)) begin
                q_rptr  <= q_rptr_next;
            end
        end
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        q_data  <= '{SCR1_IFU_Q_SIZE_HALF{'0}};
        q_err   <= '{SCR1_IFU_Q_SIZE_HALF{1'b0}};
    end else begin
        if (imem_resp_vd & ~q_flush) begin
            case (q_we)
                SCR1_WE_RDATA_HI    : begin
                    q_data  [SCR1_IFU_QUEUE_ADR_W'(q_wptr)] <= imem_rdata[31:16];
                    q_err   [SCR1_IFU_QUEUE_ADR_W'(q_wptr)] <= imem_resp_er;
                end
                SCR1_WE_RDATA_FULL  : begin
                    q_data  [SCR1_IFU_QUEUE_ADR_W'(q_wptr)] <= imem_rdata[15:0];
                    q_err   [SCR1_IFU_QUEUE_ADR_W'(q_wptr)] <= imem_resp_er;
                    q_data  [SCR1_IFU_QUEUE_ADR_W'(q_wptr + 1'b1)]  <= imem_rdata[31:16];
                    q_err   [SCR1_IFU_QUEUE_ADR_W'(q_wptr + 1'b1)]  <= imem_resp_er;
                end
            endcase // q_we
        end // write
    end
end

//-------------------------------------------------------------------------------
// RDATA logic
//-------------------------------------------------------------------------------
always_comb begin
    rdata_ident = SCR1_RDATA_NONE;

    if (imem_resp_ok & ~discard_resp) begin
        if (new_pc_unaligned) begin
            if (&imem_rdata[17:16]) begin
                rdata_ident = SCR1_RDATA_RVI_LO_NV;
            end else begin
                rdata_ident = SCR1_RDATA_RVC_NV;
            end
        end else begin // ~new_pc_unaligned
            if (rdata_curr == SCR1_RVI_PART2) begin
                if (&imem_rdata[17:16]) begin
                    rdata_ident = SCR1_RDATA_RVI_LO_RVI_HI;
                end else begin
                    rdata_ident = SCR1_RDATA_RVC_RVI_HI;
                end
            end else begin // SCR1_OTHER
                casez ({&imem_rdata[17:16], &imem_rdata[1:0]})
                    2'b?1   : rdata_ident   = SCR1_RDATA_RVI_HI_RVI_LO;
                    2'b00   : rdata_ident   = SCR1_RDATA_RVC_RVC;
                    2'b10   : rdata_ident   = SCR1_RDATA_RVI_LO_RVC;
                endcase
            end // SCR1_OTHER
        end // ~new_pc_unaligned
    end // (imem_resp_ok & ~discard_resp)
end

assign rdata_next   =   ( (rdata_ident == SCR1_RDATA_RVI_LO_NV)
                        | (rdata_ident == SCR1_RDATA_RVI_LO_RVI_HI)
                        | (rdata_ident == SCR1_RDATA_RVI_LO_RVC) ) ? SCR1_RVI_PART2 : SCR1_OTHER;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        rdata_curr  <= SCR1_OTHER;
    end else begin
        if (new_pc_req) begin
            rdata_curr  <= SCR1_OTHER;
        end else if (imem_resp_vd) begin
            rdata_curr  <= rdata_next;
        end
    end
end


//-------------------------------------------------------------------------------
// Bypass logic
//-------------------------------------------------------------------------------
`ifdef SCR1_IFU_QUEUE_BYPASS
assign instr_bypass_vd  = (instr_bypass != SCR1_BYPASS_NONE);

always_comb begin
    instr_bypass    = SCR1_BYPASS_NONE;

    if (imem_resp_vd) begin
        if (q_empty) begin
            case (rdata_ident)
                SCR1_RDATA_RVC_NV,
                SCR1_RDATA_RVC_RVC,
                SCR1_RDATA_RVI_LO_RVC       : begin
                    instr_bypass    = SCR1_BYPASS_RVC;
                end
                SCR1_RDATA_RVI_HI_RVI_LO    : begin
                    instr_bypass    = SCR1_BYPASS_RVI_RDATA;
                end
                default : begin end
            endcase // rdata_ident
        end else if ((q_ocpd_h == SCR1_IFU_Q_FREE_H_W'(1)) & q_head_rvi) begin
            if (rdata_curr == SCR1_RVI_PART2) begin
                instr_bypass    = SCR1_BYPASS_RVI_RDATA_QUEUE;
            end
        end
    end // imem_resp_vd
end
`endif // SCR1_IFU_QUEUE_BYPASS


//-------------------------------------------------------------------------------
// Instruction memory interface logic
//-------------------------------------------------------------------------------

assign imem_req = (new_pc_req & ~num_txns_pending_full) |
(
    (fsm == SCR1_FSM_FETCH) &
    ~num_txns_pending_full &
    (SCR1_TXN_CNT_W'(q_free_w_next) > num_vd_txns_pending)
);

assign imem_cmd                 = SCR1_MEM_CMD_RD;
assign imem_addr                = {(new_pc_req ? new_pc[`SCR1_XLEN-1:2] : imem_addr_r), 2'b00};

assign imem_resp_er             = (imem_resp == SCR1_MEM_RESP_RDY_ER);
assign imem_resp_ok             = (imem_resp == SCR1_MEM_RESP_RDY_OK);
assign imem_resp_vd             = (imem_resp_ok | imem_resp_er) & ~discard_resp;
assign num_txns_pending_full    = &num_txns_pending;
`ifdef SCR1_CLKCTRL_EN
assign imem_txns_pending        = |num_txns_pending;
`endif // SCR1_CLKCTRL_EN


always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        imem_addr_r <= '0;
    end else begin
        if (imem_req & imem_req_ack) begin
            // if req & ack, store either incremented new_pc or incremented address
            imem_addr_r <= (new_pc_req ? new_pc[`SCR1_XLEN-1:2] : imem_addr_r) + 1'b1;
        end else if (new_pc_req) begin
            imem_addr_r <= new_pc[`SCR1_XLEN-1:2];
        end
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        num_txns_pending <= '0;
    end else begin
        case ({(imem_req & imem_req_ack), (imem_resp_ok | imem_resp_er)})
            2'b00,
            2'b11   : begin // simultaneous response and accepted request
                      end
            default : num_txns_pending <=   ((imem_resp_ok | imem_resp_er) ?
                                                (num_txns_pending - 1'b1) :
                                                (num_txns_pending + 1'b1));
        endcase
    end
end

// discard_resp_cnt sub
always_comb begin
    logic [SCR1_TXN_CNT_W-1:0]  op_a;
    logic                       op_b;

    op_a    = discard_resp_cnt;
    op_b    = 1'b0;
    if (new_pc_req) begin
        op_a    = num_txns_pending;
        op_b    = (imem_resp_ok | imem_resp_er);
    end else if (imem_resp_er) begin
        op_a    = num_txns_pending;
        op_b    = ~(imem_req & imem_req_ack);
    end else if (imem_resp_ok & discard_resp) begin
        op_a    = discard_resp_cnt;
        op_b    = 1'b1;
    end
    discard_resp_cnt_new    = op_a - op_b;
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        discard_resp_cnt <= '0;
    end else begin
        if (new_pc_req | imem_resp_er | (imem_resp_ok & discard_resp)) begin
            discard_resp_cnt    <= discard_resp_cnt_new;
        end
    end // rst_n
end

assign num_vd_txns_pending  = num_txns_pending - discard_resp_cnt;
assign discard_resp         = |discard_resp_cnt;


//-------------------------------------------------------------------------------
// Control logic
//-------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        fsm <= SCR1_FSM_IDLE;
    end else begin
        case (fsm)
            SCR1_FSM_IDLE   : begin
                if (new_pc_req & ~stop_fetch) begin
                    fsm <= SCR1_FSM_FETCH;
                end
            end
            SCR1_FSM_FETCH  : begin
                if (stop_fetch | (imem_resp_er & ~discard_resp & ~new_pc_req)) begin
                    fsm <= SCR1_FSM_IDLE;
                end
            end
        endcase // fsm
    end
end

assign ifu_busy = (fsm == SCR1_FSM_FETCH);

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        new_pc_unaligned    <= 1'b0;
    end else begin
        if (new_pc_req) begin
            new_pc_unaligned    <= new_pc[1];
        end else if (imem_resp_vd) begin
            new_pc_unaligned    <= 1'b0;
        end
    end
end

//-------------------------------------------------------------------------------
// Instruction decode unit interface
//-------------------------------------------------------------------------------
`ifdef SCR1_IFU_QUEUE_BYPASS

always_comb begin
    ifu2idu_vd          = 1'b0;
    ifu2idu_imem_err    = 1'b0;
    ifu2idu_err_rvi_hi  = 1'b0;
    if ((fsm == SCR1_FSM_FETCH) | ~q_empty) begin
        if (instr_bypass_vd) begin
            ifu2idu_vd          = 1'b1;
            ifu2idu_imem_err    = (instr_bypass == SCR1_BYPASS_RVI_RDATA_QUEUE) ? (imem_resp_er | q_err_head) : imem_resp_er;
            ifu2idu_err_rvi_hi  = (instr_bypass == SCR1_BYPASS_RVI_RDATA_QUEUE) & imem_resp_er;
        end else if (~q_empty) begin
            if (q_ocpd_h == SCR1_IFU_Q_FREE_H_W'(1)) begin
                ifu2idu_vd          = q_head_rvc | q_err_head;
                ifu2idu_imem_err    = q_err_head;
            end else begin          // 2 or more halfwords occupied
                ifu2idu_vd          = 1'b1;
                ifu2idu_imem_err    = q_err_head ? 1'b1 : (q_head_rvi & q_err_next);
                ifu2idu_err_rvi_hi  = ~q_err_head & q_head_rvi & q_err_next;
            end
        end // ~q_empty
    end
`ifdef SCR1_DBGC_EN
    if (fetch_dbgc) begin
        ifu2idu_vd          = 1'b1;
        ifu2idu_imem_err    = 1'b0;
    end
`endif // SCR1_DBGC_EN
end

always_comb begin
    case (instr_bypass)
        SCR1_BYPASS_RVC             : begin
            ifu2idu_instr   = `SCR1_IMEM_DWIDTH'(new_pc_unaligned ? imem_rdata[31:16] : imem_rdata[15:0]);
        end
        SCR1_BYPASS_RVI_RDATA       : begin
            ifu2idu_instr   = imem_rdata;
        end
        SCR1_BYPASS_RVI_RDATA_QUEUE : begin
            ifu2idu_instr   = {imem_rdata[15:0], q_data_head};
        end
        default                     : begin
            ifu2idu_instr   = `SCR1_IMEM_DWIDTH'(q_head_rvc ? q_data_head : {q_data_next, q_data_head});
        end
    endcase // instr_bypass
`ifdef SCR1_DBGC_EN
    if (fetch_dbgc) begin
        ifu2idu_instr = dbgc_instr;
    end
`endif // SCR1_DBGC_EN
end

`else   // SCR1_IFU_QUEUE_BYPASS

always_comb begin
    ifu2idu_vd          = 1'b0;
    ifu2idu_imem_err    = 1'b0;
    ifu2idu_err_rvi_hi  = 1'b0;
    if (~q_empty) begin
        if (q_ocpd_h == SCR1_IFU_Q_FREE_H_W'(1)) begin
            ifu2idu_vd          = q_head_rvc | q_err_head;
            ifu2idu_imem_err    = q_err_head;
        end else begin          // 2 or more halfwords occupied
            ifu2idu_vd          = 1'b1;
            ifu2idu_imem_err    = q_err_head ? 1'b1 : (q_head_rvi & q_err_next);
            ifu2idu_err_rvi_hi  = ~q_err_head & q_head_rvi & q_err_next;
        end
    end // ~q_empty
`ifdef SCR1_DBGC_EN
    if (fetch_dbgc) begin
        ifu2idu_vd          = 1'b1;
        ifu2idu_imem_err    = 1'b0;
    end
`endif // SCR1_DBGC_EN
end

always_comb begin
    ifu2idu_instr = q_head_rvc ? `SCR1_IMEM_DWIDTH'(q_data_head) : {q_data_next, q_data_head};
`ifdef SCR1_DBGC_EN
    if (fetch_dbgc) begin
        ifu2idu_instr = dbgc_instr;
    end
`endif // SCR1_DBGC_EN
end

`endif  // SCR1_IFU_QUEUE_BYPASS


`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks

SCR1_SVA_IFU_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({imem_req_ack, idu2ifu_rdy, new_pc_req})
    ) else $error("IFU Error: unknown values");

SCR1_SVA_IFU_XCHECK_REQ : assert property (
    @(negedge clk) disable iff (~rst_n)
    imem_req |-> !$isunknown({imem_addr, imem_cmd})
    ) else $error("IFU Error: unknown {imem_addr, imem_cmd}");

// Behavior checks

SCR1_SVA_IFU_DRC_UNDERFLOW : assert property (
    @(negedge clk) disable iff (~rst_n)
    ~discard_resp |=> ~(discard_resp_cnt == SCR1_TXN_CNT_W'('1))
    ) else $error("IFU Error: discard_resp_cnt underflow");

SCR1_SVA_IFU_DRC_RANGE : assert property (
    @(negedge clk) disable iff (~rst_n)
    (discard_resp_cnt >= 0) & (discard_resp_cnt <= num_txns_pending)
    ) else $error("IFU Error: discard_resp_cnt out of range");

SCR1_SVA_IFU_QUEUE_OVF : assert property (
    @(negedge clk) disable iff (~rst_n)
    (q_ocpd_h >= (SCR1_IFU_Q_SIZE_HALF-1)) |->
    ((q_ocpd_h == (SCR1_IFU_Q_SIZE_HALF-1)) ? (q_we != SCR1_WE_RDATA_FULL) : (q_we == SCR1_WE_NONE))
    ) else $error("IFU Error: queue overflow");

SCR1_SVA_IFU_IMEM_ERR_BEH : assert property (
    @(negedge clk) disable iff (~rst_n)
    (imem_resp_er & ~discard_resp & ~new_pc_req) |=>
    (fsm == SCR1_FSM_IDLE) & (discard_resp_cnt == num_txns_pending)
    ) else $error("IFU Error: incorrect behavior after memory error");

SCR1_SVA_IFU_NEW_PC_REQ_BEH : assert property (
    @(negedge clk) disable iff (~rst_n)
    new_pc_req |=> q_empty
    ) else $error("IFU Error: incorrect behavior after new_pc_req");

SCR1_SVA_IFU_IMEM_ADDR_ALIGNED : assert property (
    @(negedge clk) disable iff (~rst_n)
    imem_req |-> ~|imem_addr[1:0]
    ) else $error("IFU Error: unaligned IMEM access");

SCR1_SVA_IFU_STOP_FETCH : assert property (
    @(negedge clk) disable iff (~rst_n)
    stop_fetch |=> (fsm == SCR1_FSM_IDLE)
    ) else $error("IFU Error: fetch not stopped");

SCR1_SVA_IFU_IMEM_FAULT_RVI_HI : assert property (
    @(negedge clk) disable iff (~rst_n)
    ifu2idu_err_rvi_hi |-> ifu2idu_imem_err
    ) else $error("IFU Error: ifu2idu_imem_err == 0");

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_ifu

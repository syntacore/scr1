/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_timer.sv>
/// @brief      Memory-mapped Timer
///

`include "scr1_arch_description.svh"
`include "scr1_memif.svh"

module scr1_timer (
    // Common
    input   logic                                   rst_n,
    input   logic                                   clk,
    input   logic                                   rtc_clk,

    // Memory interface
    input   logic                                   dmem_req,
    input   type_scr1_mem_cmd_e                     dmem_cmd,
    input   type_scr1_mem_width_e                   dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]           dmem_addr,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]           dmem_wdata,
    output  logic                                   dmem_req_ack,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]           dmem_rdata,
    output  type_scr1_mem_resp_e                    dmem_resp,

    // Timer interface
    output  logic [63:0]                            timer_val,
    output  logic                                   timer_irq
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------
localparam int unsigned SCR1_TIMER_ADDR_WIDTH                               = 5;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_CONTROL             = 5'h0;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_DIVIDER             = 5'h4;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMELO             = 5'h8;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMEHI             = 5'hC;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMECMPLO          = 5'h10;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMECMPHI          = 5'h14;

localparam int unsigned SCR1_TIMER_CONTROL_EN_OFFSET                        = 0;
localparam int unsigned SCR1_TIMER_CONTROL_CLKSRC_OFFSET                    = 1;
localparam int unsigned SCR1_TIMER_DIVIDER_WIDTH                            = 10;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic [63:0]                                        mtime_reg;
logic [63:0]                                        mtime_new;
logic [63:0]                                        mtimecmp_reg;
logic [63:0]                                        mtimecmp_new;
logic                                               timer_en;
logic                                               timer_clksrc_rtc;
logic [SCR1_TIMER_DIVIDER_WIDTH-1:0]                timer_div;

logic                                               control_up;
logic                                               divider_up;
logic                                               mtimelo_up;
logic                                               mtimehi_up;
logic                                               mtimecmplo_up;
logic                                               mtimecmphi_up;

logic                                               dmem_req_valid;

logic [3:0]                                         rtc_sync;
logic                                               rtc_ext_pulse;
logic [SCR1_TIMER_DIVIDER_WIDTH-1:0]                timeclk_cnt;
logic                                               timeclk_cnt_en;
logic                                               time_posedge;
logic                                               time_cmp_flag;

//-------------------------------------------------------------------------------
// Registers
//-------------------------------------------------------------------------------

// CONTROL
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        timer_en            <= 1'b1;
        timer_clksrc_rtc    <= 1'b0;
    end else begin
        if (control_up) begin
            timer_en            <= dmem_wdata[SCR1_TIMER_CONTROL_EN_OFFSET];
            timer_clksrc_rtc    <= dmem_wdata[SCR1_TIMER_CONTROL_CLKSRC_OFFSET];
        end
    end
end

// DIVIDER
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        timer_div   <= '0;
    end else begin
        if (divider_up) begin
            timer_div   <= dmem_wdata[SCR1_TIMER_DIVIDER_WIDTH-1:0];
        end
    end
end

// MTIME
assign time_posedge = (timeclk_cnt_en & (timeclk_cnt == 0));

always_comb begin
    mtime_new   = mtime_reg;
    if (time_posedge) begin
        mtime_new   = mtime_reg + 1'b1;
    end
    if (mtimelo_up) begin
        mtime_new[31:0]     = dmem_wdata;
    end
    if (mtimehi_up) begin
        mtime_new[63:32]    = dmem_wdata;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mtime_reg   <= '0;
    end else begin
        if (time_posedge | mtimelo_up | mtimehi_up) begin
            mtime_reg   <= mtime_new;
        end
    end
end

// MTIMECMP
always_comb begin
    mtimecmp_new    = mtimecmp_reg;
    if (mtimecmplo_up) begin
        mtimecmp_new[31:0]  = dmem_wdata;
    end
    if (mtimecmphi_up) begin
        mtimecmp_new[63:32] = dmem_wdata;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mtimecmp_reg    <= '0;
    end else begin
        if (mtimecmplo_up | mtimecmphi_up) begin
            mtimecmp_reg    <= mtimecmp_new;
        end
    end
end

//-------------------------------------------------------------------------------
// Interrupt pending
//-------------------------------------------------------------------------------
assign time_cmp_flag = (mtime_reg >= ((mtimecmplo_up | mtimecmphi_up) ? mtimecmp_new : mtimecmp_reg));

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        timer_irq   <= 1'b0;
    end else begin
        if (~timer_irq) begin
            timer_irq   <= time_cmp_flag;
        end else begin // 1'b1
            if (mtimecmplo_up | mtimecmphi_up) begin
                timer_irq   <= time_cmp_flag;
            end
        end
    end
end

//-------------------------------------------------------------------------------
// Timer divider
//-------------------------------------------------------------------------------
assign timeclk_cnt_en   = (~timer_clksrc_rtc ? 1'b1 : rtc_ext_pulse) & timer_en;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        timeclk_cnt <= '0;
    end else begin
        case (1'b1)
            divider_up      : timeclk_cnt   <= dmem_wdata[SCR1_TIMER_DIVIDER_WIDTH-1:0];
            time_posedge    : timeclk_cnt   <= timer_div;
            timeclk_cnt_en  : timeclk_cnt   <= timeclk_cnt - 1'b1;
            default         : begin end
        endcase
    end
end

//-------------------------------------------------------------------------------
// RTC synchronization
//-------------------------------------------------------------------------------
assign rtc_ext_pulse    = rtc_sync[3] ^ rtc_sync[2];

always_ff @(negedge rst_n, posedge rtc_clk) begin
    if (~rst_n) begin
        rtc_sync[0] <= 1'b0;
    end else begin
        if (timer_clksrc_rtc) begin
            rtc_sync[0] <= ~rtc_sync[0];
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        rtc_sync[3:1]   <= '0;
    end else begin
        if (timer_clksrc_rtc) begin
            rtc_sync[3:1]   <= rtc_sync[2:0];
        end
    end
end

//-------------------------------------------------------------------------------
// Memory interface
//-------------------------------------------------------------------------------
assign dmem_req_valid   =   (dmem_width == SCR1_MEM_WIDTH_WORD) & (~|dmem_addr[1:0]) &
                            (dmem_addr[SCR1_TIMER_ADDR_WIDTH-1:2] <= SCR1_TIMER_MTIMECMPHI[SCR1_TIMER_ADDR_WIDTH-1:2]);

assign dmem_req_ack     = 1'b1;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        dmem_resp   <= SCR1_MEM_RESP_NOTRDY;
        dmem_rdata  <= '0;
    end else begin
        if (dmem_req) begin
            if (dmem_req_valid) begin
                dmem_resp   <= SCR1_MEM_RESP_RDY_OK;
                if (dmem_cmd == SCR1_MEM_CMD_RD) begin
                    case (dmem_addr[SCR1_TIMER_ADDR_WIDTH-1:0])
                        SCR1_TIMER_CONTROL      : dmem_rdata    <= `SCR1_DMEM_DWIDTH'({timer_clksrc_rtc, timer_en});
                        SCR1_TIMER_DIVIDER      : dmem_rdata    <= `SCR1_DMEM_DWIDTH'(timer_div);
                        SCR1_TIMER_MTIMELO      : dmem_rdata    <= mtime_reg[31:0];
                        SCR1_TIMER_MTIMEHI      : dmem_rdata    <= mtime_reg[63:32];
                        SCR1_TIMER_MTIMECMPLO   : dmem_rdata    <= mtimecmp_reg[31:0];
                        SCR1_TIMER_MTIMECMPHI   : dmem_rdata    <= mtimecmp_reg[63:32];
                        default                 : begin end
                    endcase
                end
            end else begin
                dmem_resp   <= SCR1_MEM_RESP_RDY_ER;
            end
        end else begin
            dmem_resp   <= SCR1_MEM_RESP_NOTRDY;
            dmem_rdata  <= '0;
        end
    end
end

always_comb begin
    control_up      = 1'b0;
    divider_up      = 1'b0;
    mtimelo_up      = 1'b0;
    mtimehi_up      = 1'b0;
    mtimecmplo_up   = 1'b0;
    mtimecmphi_up   = 1'b0;
    if (dmem_req & dmem_req_valid & (dmem_cmd == SCR1_MEM_CMD_WR)) begin
        case (dmem_addr[SCR1_TIMER_ADDR_WIDTH-1:0])
            SCR1_TIMER_CONTROL      : control_up    = 1'b1;
            SCR1_TIMER_DIVIDER      : divider_up    = 1'b1;
            SCR1_TIMER_MTIMELO      : mtimelo_up    = 1'b1;
            SCR1_TIMER_MTIMEHI      : mtimehi_up    = 1'b1;
            SCR1_TIMER_MTIMECMPLO   : mtimecmplo_up = 1'b1;
            SCR1_TIMER_MTIMECMPHI   : mtimecmphi_up = 1'b1;
            default                 : begin end
        endcase
    end
end

//-------------------------------------------------------------------------------
// Timer interface
//-------------------------------------------------------------------------------
assign timer_val    = mtime_reg;

endmodule : scr1_timer
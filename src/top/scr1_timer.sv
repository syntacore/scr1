/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_timer.sv>
/// @brief      Memory-mapped timer
///

`include "scr1_arch_description.svh"

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
localparam int unsigned SCR1_TIMER_MTIMECLKSET_DIV_WIDTH                    = 16;
localparam int unsigned SCR1_TIMER_MTIMECLKSET_CLKSEL_OFFSET                = 16;
localparam int unsigned SCR1_TIMER_MTIMECLKSET_EN_OFFSET                    = 17;
localparam logic [SCR1_TIMER_MTIMECLKSET_EN_OFFSET:0] SCR1_TIMER_MTIMECLKSET_RST_VAL    = 'h30064;

localparam int unsigned SCR1_TIMER_ADDR_WIDTH                               = 5;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIME_ADDR          = 5'h0;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMEH_ADDR         = 5'h4;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMECMP_ADDR       = 5'h8;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMECMPH_ADDR      = 5'hC;
localparam logic [SCR1_TIMER_ADDR_WIDTH-1:0] SCR1_TIMER_MTIMECLKSET_ADDR    = 5'h10;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic [63:0]                                        mtime_reg;
logic [63:0]                                        mtime_new;
logic [63:0]                                        mtimecmp_reg;
logic [63:0]                                        mtimecmp_new;
logic [SCR1_TIMER_MTIMECLKSET_EN_OFFSET:0]          mtimeclkset_reg;

logic                                               mtime_up;
logic                                               mtimeh_up;
logic                                               mtimecmp_up;
logic                                               mtimecmph_up;
logic                                               mtimeclkset_up;

logic                                               dmem_req_valid;
logic                                               timer_en;
logic [SCR1_TIMER_MTIMECLKSET_DIV_WIDTH-1:0]        timer_div;
logic                                               rtc_internal;
logic [3:0]                                         rtc_sync;
logic                                               rtc_ext_pulse;
logic [SCR1_TIMER_MTIMECLKSET_DIV_WIDTH-1:0]        timeclk_cnt;
logic                                               timeclk_cnt_en;
logic                                               time_posedge;
logic                                               time_cmp_flag;

//-------------------------------------------------------------------------------
// Registers
//-------------------------------------------------------------------------------

// MTIME[H] registers
assign time_posedge = (timeclk_cnt_en & ~|timeclk_cnt[SCR1_TIMER_MTIMECLKSET_DIV_WIDTH-1:1]);

always_comb begin
    mtime_new   = mtime_reg;
    if (time_posedge) begin
        mtime_new   = mtime_reg + 1'b1;
    end
    if (mtime_up) begin
        mtime_new[31:0]     = dmem_wdata;
    end
    if (mtimeh_up) begin
        mtime_new[63:32]    = dmem_wdata;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mtime_reg   <= '0;
    end else begin
        if (time_posedge | mtime_up | mtimeh_up) begin
            mtime_reg   <= mtime_new;
        end
    end
end

// MTIMECMP[H] registers
always_comb begin
    mtimecmp_new    = mtimecmp_reg;
    if (mtimecmp_up) begin
        mtimecmp_new[31:0]  = dmem_wdata;
    end
    if (mtimecmph_up) begin
        mtimecmp_new[63:32] = dmem_wdata;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mtimecmp_reg    <= '1;
    end else begin
        if (mtimecmp_up | mtimecmph_up) begin
            mtimecmp_reg    <= mtimecmp_new;
        end
    end
end

// MTIMECLKSET register
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        mtimeclkset_reg <= SCR1_TIMER_MTIMECLKSET_RST_VAL;
    end else begin
        if (mtimeclkset_up) begin
            mtimeclkset_reg     <= dmem_wdata[SCR1_TIMER_MTIMECLKSET_EN_OFFSET:0];
        end
    end
end

assign timer_div    = mtimeclkset_reg[SCR1_TIMER_MTIMECLKSET_DIV_WIDTH-1:0];
assign timer_en     = mtimeclkset_reg[SCR1_TIMER_MTIMECLKSET_EN_OFFSET];
assign rtc_internal = mtimeclkset_reg[SCR1_TIMER_MTIMECLKSET_CLKSEL_OFFSET];

//-------------------------------------------------------------------------------
// Interrupt pending
//-------------------------------------------------------------------------------
assign time_cmp_flag = (mtime_reg >= ((mtimecmp_up | mtimecmph_up) ? mtimecmp_new : mtimecmp_reg));

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        timer_irq   <= 1'b0;
    end else begin
        if (~timer_irq) begin
            timer_irq   <= time_cmp_flag;
        end else begin // 1'b1
            if (mtimecmp_up | mtimecmph_up) begin
                timer_irq   <= time_cmp_flag;
            end
        end
    end
end

//-------------------------------------------------------------------------------
// Timer divider
//-------------------------------------------------------------------------------
assign timeclk_cnt_en   = (rtc_internal ? 1'b1 : rtc_ext_pulse) & timer_en;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        timeclk_cnt <= '0;
    end else begin
        case (1'b1)
            mtimeclkset_up      : timeclk_cnt   <= dmem_wdata[SCR1_TIMER_MTIMECLKSET_DIV_WIDTH-1:0];
            time_posedge        : timeclk_cnt   <= timer_div;
            timeclk_cnt_en      : timeclk_cnt   <= timeclk_cnt - 1'b1;
            default             : begin end
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
        if (~rtc_internal) begin
            rtc_sync[0] <= ~rtc_sync[0];
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        rtc_sync[3:1]   <= '0;
    end else begin
        if (~rtc_internal) begin
            rtc_sync[3:1]   <= rtc_sync[2:0];
        end
    end
end

//-------------------------------------------------------------------------------
// Memory interface
//-------------------------------------------------------------------------------
assign dmem_req_valid   =   (dmem_width == SCR1_MEM_WIDTH_WORD) & (~|dmem_addr[1:0]) &
                            (dmem_addr[SCR1_TIMER_ADDR_WIDTH-1:2] <= (SCR1_TIMER_MTIMECLKSET_ADDR >> 2));

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
                        SCR1_TIMER_MTIME_ADDR       : dmem_rdata    <= mtime_reg[31:0];
                        SCR1_TIMER_MTIMEH_ADDR      : dmem_rdata    <= mtime_reg[63:32];
                        SCR1_TIMER_MTIMECMP_ADDR    : dmem_rdata    <= mtimecmp_reg[31:0];
                        SCR1_TIMER_MTIMECMPH_ADDR   : dmem_rdata    <= mtimecmp_reg[63:32];
                        SCR1_TIMER_MTIMECLKSET_ADDR : dmem_rdata    <= `SCR1_DMEM_DWIDTH'(mtimeclkset_reg);
                        default                     : begin end
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
    mtime_up        = 1'b0;
    mtimeh_up       = 1'b0;
    mtimecmp_up     = 1'b0;
    mtimecmph_up    = 1'b0;
    mtimeclkset_up  = 1'b0;
    if (dmem_req & dmem_req_valid & (dmem_cmd == SCR1_MEM_CMD_WR)) begin
        case (dmem_addr[SCR1_TIMER_ADDR_WIDTH-1:0])
            SCR1_TIMER_MTIME_ADDR       : mtime_up          = 1'b1;
            SCR1_TIMER_MTIMEH_ADDR      : mtimeh_up         = 1'b1;
            SCR1_TIMER_MTIMECMP_ADDR    : mtimecmp_up       = 1'b1;
            SCR1_TIMER_MTIMECMPH_ADDR   : mtimecmph_up      = 1'b1;
            SCR1_TIMER_MTIMECLKSET_ADDR : mtimeclkset_up    = 1'b1;
            default                     : begin end
        endcase
    end
end

//-------------------------------------------------------------------------------
// Timer interface
//-------------------------------------------------------------------------------
assign timer_val    = mtime_reg;

endmodule : scr1_timer
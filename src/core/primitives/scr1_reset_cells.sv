/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_sync_rstn.sv>
/// @brief      Cells for reset handling
///

module scr1_reset_buf_cell (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_mode,
    input   logic           test_rst_n,
    input   logic           reset_n_in,
    output  logic           reset_n_out,
    output  logic           reset_n_status
);

logic       reset_n_ff;
logic       reset_n_status_ff;
logic       rst_n_mux;

assign rst_n_mux = (test_mode == 1'b1) ? test_rst_n : rst_n;

always_ff @(negedge rst_n_mux, posedge clk) begin
    if (~rst_n_mux) begin
        reset_n_ff <= 1'b0;
    end else begin
        reset_n_ff <= reset_n_in;
    end
end

assign reset_n_out = (test_mode == 1'b1) ? test_rst_n : reset_n_ff;

always_ff @(negedge rst_n_mux, posedge clk) begin
    if (~rst_n_mux) begin
        reset_n_status_ff <= 1'b0;
    end else begin
        reset_n_status_ff <= reset_n_in;
    end
end
assign reset_n_status = reset_n_status_ff;

endmodule : scr1_reset_buf_cell


module scr1_reset_sync_cell (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_rst_n,
    input   logic           test_mode,
    output  logic           rst_n_out
);

logic [1:0] rst_n_dff;
logic       local_rst_n_in;

assign local_rst_n_in = (test_mode == 1'b1) ? test_rst_n : rst_n;

always_ff @(negedge local_rst_n_in, posedge clk) begin
    if (~local_rst_n_in) begin
        rst_n_dff <= '0;
    end else begin
        rst_n_dff[0] <= 1'b1;
        rst_n_dff[1] <= rst_n_dff[0];
    end
end

assign rst_n_out = (test_mode == 1'b1) ? test_rst_n : rst_n_dff[1];

endmodule : scr1_reset_sync_cell


module scr1_reset_buf_qlfy_cell (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_rst_n,
    input   logic           test_mode,
    input   logic           reset_n_in,
    output  logic           reset_n_out_qlfy,
    output  logic           reset_n_out,
    output  logic           reset_n_status
);

logic rst_n_mux;
logic reset_n_in_mux;
logic reset_n_front_ff;
logic reset_n_victim_ff;
logic reset_n_qualifier_ff;
logic reset_n_lucky_ff;
logic reset_n_status_ff;

// Front async stage
assign reset_n_in_mux = (test_mode == 1'b1) ? test_rst_n : (rst_n & reset_n_in);

always_ff @(negedge reset_n_in_mux, posedge clk) begin
    if (~reset_n_in_mux) begin
        reset_n_front_ff    <= 1'b0;
    end else begin
        reset_n_front_ff    <= 1'b1;
    end
end

// Core sync stages
assign rst_n_mux = (test_mode == 1'b1) ? test_rst_n : rst_n;

always_ff @(negedge rst_n_mux, posedge clk) begin
    if (~rst_n_mux) begin
        reset_n_victim_ff    <= 1'b0;
        reset_n_qualifier_ff <= 1'b0;
        reset_n_lucky_ff     <= 1'b0;
    end else begin
        reset_n_victim_ff    <= reset_n_front_ff;
        reset_n_qualifier_ff <= reset_n_victim_ff;
        reset_n_lucky_ff     <= reset_n_qualifier_ff;
    end
end

assign reset_n_out_qlfy = reset_n_qualifier_ff;
assign reset_n_out      = (test_mode == 1'b1) ? test_rst_n : reset_n_lucky_ff;

// Reset status stage
always_ff @(negedge rst_n_mux, posedge clk) begin
    if (~rst_n_mux) begin
        reset_n_status_ff    <= 1'b0;
    end else begin
        reset_n_status_ff    <= reset_n_qualifier_ff;
    end
end
assign reset_n_status = reset_n_status_ff;

endmodule : scr1_reset_buf_qlfy_cell


module scr1_reset_and2_cell (
    input   logic [1:0]     rst_n_in,
    input   logic           test_rst_n,
    input   logic           test_mode,
    output  logic           rst_n_out
);

assign rst_n_out = (test_mode == 1'b1) ? test_rst_n : (&rst_n_in);

endmodule : scr1_reset_and2_cell


module scr1_reset_and3_cell (
    input   logic [2:0]     rst_n_in,
    input   logic           test_rst_n,
    input   logic           test_mode,
    output  logic           rst_n_out
);

assign rst_n_out = (test_mode == 1'b1) ? test_rst_n : (&rst_n_in);

endmodule : scr1_reset_and3_cell


module scr1_reset_mux2_cell (
    input   logic [1:0]     rst_n_in,
    input   logic           select,
    input   logic           test_rst_n,
    input   logic           test_mode,
    output  logic           rst_n_out
);

assign rst_n_out = (test_mode == 1'b1) ? test_rst_n : rst_n_in[select];

endmodule : scr1_reset_mux2_cell
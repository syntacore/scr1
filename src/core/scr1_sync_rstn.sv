/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_sync_rstn.sv>
/// @brief      Synchronizer for rst_n with test_mode
///

module scr1_sync_rstn (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_mode,
    input   logic           rst_n_din,
    output  logic           rst_n_dout,
    output  logic           rst_n_status
);

logic       local_rst_n;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        local_rst_n <= 1'b0;
    end else begin
        local_rst_n <= rst_n_din;
    end
end

assign rst_n_dout = (test_mode) ? rst_n : local_rst_n;

always_ff @(posedge clk, negedge rst_n_dout) begin
    if (~rst_n_dout) begin
        rst_n_status <= 1'b0;
    end else begin
        rst_n_status <= 1'b1;
    end
end

endmodule : scr1_sync_rstn

/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_sync_rstn.sv>
/// @brief      Cells for reset handling
///

//--------------------------------------------------------------------
// Reset Buffer Cell
//--------------------------------------------------------------------
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

//--------------------------------------------------------------------
// Reset CDC Synchronization Cell
//--------------------------------------------------------------------
module scr1_reset_sync_cell #(
    parameter int unsigned STAGES_AMOUNT = 2
) (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_rst_n,
    input   logic           test_mode,
    input   logic           rst_n_in,
    output  logic           rst_n_out
);

logic [STAGES_AMOUNT-1:0]   rst_n_dff;
logic                       local_rst_n_in;

assign local_rst_n_in = (test_mode == 1'b1) ? test_rst_n : rst_n;

generate

if (STAGES_AMOUNT == 1)

begin : gen_reset_sync_cell_single
    always_ff @(negedge local_rst_n_in, posedge clk) begin
        if (~local_rst_n_in) begin
            rst_n_dff <= 1'b0;
        end else begin
            rst_n_dff <= rst_n_in;
        end
    end
end : gen_reset_sync_cell_single

else // STAGES_AMOUNT > 1

begin : gen_reset_sync_cell_multi
    always_ff @(negedge local_rst_n_in, posedge clk)
    begin
        if (~local_rst_n_in) begin
            rst_n_dff <= '0;
        end else begin
            rst_n_dff <= {rst_n_dff[STAGES_AMOUNT-2:0], rst_n_in};
        end
    end
end : gen_reset_sync_cell_multi

endgenerate

assign rst_n_out = (test_mode == 1'b1) ? test_rst_n : rst_n_dff[STAGES_AMOUNT-1];

endmodule : scr1_reset_sync_cell

//--------------------------------------------------------------------
// Data CDC/RDC Synchronization Cell
//--------------------------------------------------------------------
module scr1_data_sync_cell #(
    parameter int unsigned  STAGES_AMOUNT = 1
) (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           data_in,
    output  logic           data_out
);

logic [STAGES_AMOUNT-1:0] data_dff;

generate

if (STAGES_AMOUNT == 1)

begin : gen_data_sync_cell_single
    always_ff @(negedge rst_n, posedge clk)
    begin
        if (~rst_n) begin
            data_dff <= 1'b0;
        end else begin
            data_dff <= data_in;
        end
    end
end : gen_data_sync_cell_single

else // STAGES_AMOUNT > 1

begin : gen_data_sync_cell_multi
    always_ff @(negedge rst_n, posedge clk)
    begin
        if (~rst_n) begin
            data_dff <= '0;
        end else begin
            data_dff <= {data_dff[STAGES_AMOUNT-2:0], data_in};
        end
    end
end : gen_data_sync_cell_multi

endgenerate

assign data_out = data_dff[STAGES_AMOUNT-1];

endmodule : scr1_data_sync_cell

//--------------------------------------------------------------------
// Reset / RDC Qualifyer Adapter Cell
//   (Reset Generation Cell w/ RDC Qualifyer Adaptation circuitry)
//--------------------------------------------------------------------
// Total stages amount =
//    1 Front Sync stage \
//  + 1 (delay introduced by the reset output buffer register)
//--------------------------------------------------------------------
module scr1_reset_qlfy_adapter_cell_sync (
    input   logic           rst_n,
    input   logic           clk,
    input   logic           test_rst_n,
    input   logic           test_mode,
    input   logic           reset_n_in_sync,
    output  logic           reset_n_out_qlfy,
    output  logic           reset_n_out,
    output  logic           reset_n_status
);

logic rst_n_mux;
logic reset_n_front_ff;

// Front sync stage
assign rst_n_mux = (test_mode == 1'b1) ? test_rst_n : rst_n;

always_ff @(negedge rst_n_mux, posedge clk) begin
    if (~rst_n_mux) begin
        reset_n_front_ff    <= 1'b0;
    end else begin
        reset_n_front_ff    <= reset_n_in_sync;
    end
end

//   Sync reset output for all reset qualifier chains targeting this reset domain
// (for reset-domain-crossings with the given reset domain as a destination).
assign reset_n_out_qlfy = reset_n_front_ff;

// Reset output buffer
scr1_reset_buf_cell
i_reset_output_buf (
    .rst_n              (rst_n),
    .clk                (clk),
    .test_mode          (test_mode),
    .test_rst_n         (test_rst_n),
    .reset_n_in         (reset_n_front_ff),
    .reset_n_out        (reset_n_out),
    .reset_n_status     (reset_n_status)
);

endmodule : scr1_reset_qlfy_adapter_cell_sync

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
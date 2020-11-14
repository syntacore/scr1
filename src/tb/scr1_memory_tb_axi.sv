/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_memory_tb_axi.sv>
/// @brief      AXI memory testbench
///

`include "scr1_arch_description.svh"
`include "scr1_ipic.svh"

module scr1_memory_tb_axi #(
    parameter SIZE   = 1*1024*1024,
    parameter N_IF   = 2,
    parameter W_ID   = 4,
    parameter W_ADR  = 32,
    parameter W_DATA = 32
)
(
    // System
    input   logic                          rst_n,
    input   logic                          clk,
`ifdef SCR1_IPIC_EN
    output  logic [SCR1_IRQ_LINES_NUM-1:0] irq_lines,
`else // SCR1_IPIC_EN
    output  logic                          ext_irq,
`endif // SCR1_IPIC_EN
    output  logic                          soft_irq,

    // Write address channel
    input  logic [N_IF-1:0]                awvalid,
    input  logic [N_IF-1:0] [W_ID-1:0]     awid,
    input  logic [N_IF-1:0] [W_ADR-1:0]    awaddr,
    input  logic [N_IF-1:0] [2:0]          awsize,
    input  logic [N_IF-1:0] [7:0]          awlen,
    output logic [N_IF-1:0]                awready,

    // Write data channel
    input  logic [N_IF-1:0]                wvalid,
    input  logic [N_IF-1:0] [W_DATA-1:0]   wdata,
    input  logic [N_IF-1:0] [W_DATA/8-1:0] wstrb,
    input  logic [N_IF-1:0]                wlast,
    output logic [N_IF-1:0]                wready,

    // Write response channel
    input  logic [N_IF-1:0]                bready,
    output logic [N_IF-1:0]                bvalid,
    output logic [N_IF-1:0] [W_ID-1:0]     bid,
    output logic [N_IF-1:0] [1:0]          bresp,

    // Read address channel
    input  logic [N_IF-1:0]                arvalid,
    input  logic [N_IF-1:0] [W_ID-1:0]     arid,
    input  logic [N_IF-1:0] [W_ADR-1:0]    araddr,
    input  logic [N_IF-1:0] [1:0]          arburst,
    input  logic [N_IF-1:0] [2:0]          arsize,
    input  logic [N_IF-1:0] [7:0]          arlen,
    output logic [N_IF-1:0]                arready,

    // Read data channel
    input  logic [N_IF-1:0]                rready,
    output logic [N_IF-1:0]                rvalid,
    output logic [N_IF-1:0] [W_ID-1:0]     rid,
    output logic [N_IF-1:0] [W_DATA-1:0]   rdata,
    output logic [N_IF-1:0]                rlast,
    output logic [N_IF-1:0] [1:0]          rresp
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic  [7:0]                                memory [0:SIZE-1];
logic  [N_IF-1:0] [W_ADR-1:0]               awaddr_hold;
logic  [N_IF-1:0] [2:0]                     awsize_hold;
genvar                                      gi;
genvar                                      gj;

`ifdef SCR1_IPIC_EN
logic [SCR1_IRQ_LINES_NUM-1:0]              irq_lines_reg;
`else // SCR1_IPIC_EN
logic                                       ext_irq_reg;
`endif // SCR1_IPIC_EN
logic                                       soft_irq_reg;

`ifdef VERILATOR
logic [255:0]                               test_file;
`else // VERILATOR
string                                      test_file;
`endif // VERILATOR
bit                                         test_file_init;

//-------------------------------------------------------------------------------
// Local functions
//-------------------------------------------------------------------------------

function automatic logic [W_DATA-1:0] mem_read (
    logic [W_ADR:0] adr,        // starting address of READ burst operation
    int             bytes_num,  // number of bytes to read
    int             bytes_max   // number of bytes in data width
    );

    logic [W_ADR:0] byte_lane;  // positional number of byte to read

    mem_read  = 'x;
    byte_lane = 0;

    // Storing the positional number of byte to read
    for(int i=0; i<$clog2(bytes_max); ++i) begin
        byte_lane[i] = adr[i];
    end

    // READ burst operation
    for(int i=byte_lane; i<bytes_max & bytes_num!=0; ++i) begin
        // Reading Soft IRQ value
        if (adr[W_ADR-1:1] == SCR1_SIM_SOFT_IRQ_ADDR[W_ADR-1:1]) begin
            mem_read[0] = soft_irq_reg;
`ifdef SCR1_IPIC_EN
        // Reading IRQ Lines values
        end else if (adr[W_ADR-1:1] == SCR1_SIM_EXT_IRQ_ADDR[W_ADR-1:1]) begin
            if (i*8 < SCR1_IRQ_LINES_NUM) begin
                if (SCR1_IRQ_LINES_NUM < 8) begin
                    mem_read[(i*8)+:8] = irq_lines_reg;
                end else begin
                    mem_read[(i*8)+:8] = irq_lines_reg[(i*8)+:8];
                end
            end
`else // SCR1_IPIC_EN
        // Reading External IRQ value
        end else if (adr[W_ADR-1:1] == SCR1_SIM_EXT_IRQ_ADDR[W_ADR-1:1]) begin
            mem_read[0] = ext_irq_reg;
`endif // SCR1_IPIC_EN
        // Regular read operation
        end else begin
            mem_read[(i*8)+:8] = memory[adr];
        end

        adr = adr+1'b1;
        bytes_num = bytes_num - 1'b1;
    end
endfunction : mem_read

function automatic void mem_write (
    logic [W_ADR-1:0]      adr,         // starting address of WRITE burst operation
    logic [W_DATA-1:0]     data,        // data to write
    logic [(W_DATA/8)-1:0] bytes_en,    // bytes write strobes
    int                    bytes_num,   // number of bytes to write
    int                    bytes_max    // number of bytes in data width
    );

    logic[W_ADR:0]         byte_lane;   // positional number of byte to write

    byte_lane = 0;

    // Storing the positional number of byte to write
    for(int i=0; i<$clog2(bytes_max); ++i) begin
        byte_lane[i] = adr[i];
    end

    // WRITE burst operation
    for(int i=byte_lane; i<bytes_max & bytes_num!=0; ++i) begin
        // Printing character in the simulation console
        if(bytes_en[i] & adr == SCR1_SIM_PRINT_ADDR) begin
            $write("%c",data[(i*8)+:8]);
        // Writing Soft IRQ value
        end else if(bytes_en[0] & adr[W_ADR-1:1] == SCR1_SIM_SOFT_IRQ_ADDR[W_ADR-1:1]) begin
            soft_irq_reg <= data[0];
`ifdef SCR1_IPIC_EN
        // Writing IRQ Lines values
        end else if(bytes_en[i] & adr[W_ADR-1:1] == SCR1_SIM_EXT_IRQ_ADDR[W_ADR-1:1]) begin
            if( i*8 < SCR1_IRQ_LINES_NUM ) begin
                if( SCR1_IRQ_LINES_NUM < 8 ) begin
                    irq_lines_reg <= data[SCR1_IRQ_LINES_NUM-1:0];
                end else begin
                    irq_lines_reg[(i*8)+:8] <= data[(i*8)+:8];
                end
            end
`else
        // Writing External IRQ value
        end else if(bytes_en[0] & adr[W_ADR-1:1] == SCR1_SIM_EXT_IRQ_ADDR[W_ADR-1:1]) begin
            ext_irq_reg <= data[0];
`endif // SCR1_IPIC_EN
        // Regular write operation
        end else if (bytes_en[i]) begin
            memory[adr] = data[(i*8)+:8];
        end
        adr       = adr+1'b1;
        bytes_num = bytes_num-1'b1;
    end
endfunction : mem_write


`ifdef SCR1_IPIC_EN
assign irq_lines = irq_lines_reg;
`else // SCR1_IPIC_EN
assign ext_irq = ext_irq_reg;
`endif // SCR1_IPIC_EN
assign soft_irq = soft_irq_reg;

generate for(gi=0; gi<N_IF; ++gi) begin : rw_if

//-------------------------------------------------------------------------------
// Read operation
//-------------------------------------------------------------------------------
always @(posedge clk, negedge rst_n) begin
    if(~rst_n) begin
        arready[gi] <= 1'b1;
        rvalid[gi]  <= 1'b0;
        rresp[gi]   <= 2'd3;
        rdata[gi]   <= 'x;
        rlast[gi]   <= 1'b0;
        rid[gi]     <= '0;
    end else begin

        // Read data: acked
        if( rvalid[gi] & rready[gi] ) begin
            arready[gi] <= 1'b1;
            rvalid[gi]  <= 1'b0;
        end else if( rvalid[gi] & !rready[gi] ) begin
            arready[gi] <= 1'b0;
        end

        // Read data: valid
        if( arvalid[gi] & arready[gi] & ~(rvalid[gi] & !rready[gi]) ) begin

            rvalid[gi] <= 1'b1;
            rresp[gi]  <= '0;
            rlast[gi]  <= 1'b1;
            rid[gi]    <= arid[gi];

            rdata[gi]  <= mem_read( araddr[gi],
                                    2**arsize[gi],
                                    W_DATA/8 );
        end
    end
end

//-------------------------------------------------------------------------------
// Write operation
//-------------------------------------------------------------------------------
always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        bvalid[gi]      <= '0;
        bresp[gi]       <= 2'd3;
        awready[gi]     <= 1'b1;
        wready[gi]      <= 1'b1;

        soft_irq_reg    <= '0;
`ifdef SCR1_IPIC_EN
        irq_lines_reg   <= '0;
`else // SCR1_IPIC_EN
        ext_irq_reg     <= '0;
`endif // SCR1_IPIC_EN

        if (test_file_init) $readmemh(test_file, memory);
    end else begin

        // Write data: response
        if( bvalid[gi] & bready[gi] ) begin
            bvalid[gi]  <= 1'b0;
            awready[gi] <= 1'b1;
            wready[gi]  <= 1'b1;
        end else if( bvalid[gi] & !bready[gi] ) begin
            awready[gi] <= 1'b0;
            wready[gi]  <= 1'b0;
        end

        // Write data: get address
        if( awvalid[gi] & awready[gi] & ~(bvalid[gi] & !bready[gi]) ) begin
            bid <= awid[gi];
            if( ~wvalid[gi] ) begin
                awaddr_hold[gi] <= awaddr[gi];
                awsize_hold[gi] <= awsize[gi];
                awready[gi] <= 1'b0;
            end
        end

        // Write data: get data
        if( wvalid[gi] & wready[gi] & wlast[gi] ) begin
            bvalid[gi] <= 1'b1;
            bresp[gi]  <= '0;

            mem_write( awready[gi] ? awaddr[gi] : awaddr_hold[gi],
                       wdata[gi],
                       wstrb[gi],
                       2**(awready[gi] ? awsize[gi] : awsize_hold[gi]),
                       W_DATA/8 );
        end
    end
end

//`ifndef VERILATOR
//-------------------------------------------------------------------------------
// Assertions
//-------------------------------------------------------------------------------
SVA_TBMEM_AWADDR_404 :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        awvalid[gi] |-> awaddr[gi]<SIZE | awaddr[gi]==SCR1_SIM_PRINT_ADDR
                                        | awaddr[gi]==SCR1_SIM_SOFT_IRQ_ADDR
                                        | awaddr[gi]==SCR1_SIM_EXT_IRQ_ADDR
    )
    else $error("TBMEM: awaddr[%0d] >= SIZE",gi);

SVA_TBMEM_X_AWVALID :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown(awvalid[gi])
    )
    else $error("TBMEM: X state on awvalid[%0d]",gi);

SVA_TBMEM_X_AWCHANNEL :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        awvalid[gi] |-> !$isunknown({awid[gi],awaddr[gi],awsize[gi],awlen[gi]})
    )
    else $error("TBMEM: X state on aw channel[%0d]",gi);

SVA_TBMEM_AWLEN :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        awvalid[gi] |-> awlen[gi]==0
    )
    else $error("TBMEM: awlen[%0d] = %0d is not supported",gi,awlen[gi]);

SVA_TBMEM_X_WVALID :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown(wvalid[gi])
    )
    else $error("TBMEM: X state on wvalid[%0d]",gi);

SVA_TBMEM_X_WCHANNEL :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        wvalid[gi] |-> !$isunknown({wstrb[gi],wlast[gi]})
    )
    else $error("TBMEM: X state on w channel[%0d]",gi);

for(gj=0; gj<W_DATA/8; ++gj) begin : SVA_TBMEM_X_WSTRB
WDATA :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        (wvalid[gi] & wstrb[gi][gj]) |-> !$isunknown(wdata[gi][(gj*8)+:8])
    )
    else $error("TBMEM: X state on wdata with wstrb[%0d][%0d]",gi,gj);
end

SVA_TBMEM_X_BREADY :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        bvalid[gi] |-> !$isunknown(bready[gi])
    )
    else $error("TBMEM: X state on bready[%0d]",gi);

SVA_TBMEM_ARADDR_404 :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        arvalid[gi] |-> araddr[gi]<SIZE | araddr[gi]==SCR1_SIM_PRINT_ADDR
                                        | awaddr[gi]==SCR1_SIM_SOFT_IRQ_ADDR
                                        | awaddr[gi]==SCR1_SIM_EXT_IRQ_ADDR
    )
    else $error("TBMEM: awaddr[%0d] >= SIZE",gi);

SVA_TBMEM_X_ARVALID :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown(arvalid[gi])
    )
    else $error("TBMEM: X state on arvalid[%0d]",gi);

SVA_TBMEM_X_ARCHANNEL :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        arvalid[gi] |-> !$isunknown({arid[gi],araddr[gi],arsize[gi],arlen[gi]})
    )
    else $error("TBMEM: X state on ar channel[%0d]",gi);

SVA_TBMEM_ARLEN :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        arvalid[gi] |-> arlen[gi]==0
    )
    else $error("TBMEM: arlen[%0d] = %0d is not supported",gi,arlen[gi]);

SVA_TBMEM_X_RREADY :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        rvalid[gi] |-> !$isunknown(rready[gi])
    )
    else $error("TBMEM: X state on rready[%0d]",gi);

//`endif // VERILATOR

end endgenerate

endmodule : scr1_memory_tb_axi

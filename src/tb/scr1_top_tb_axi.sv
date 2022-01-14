/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_top_tb_axi.sv>
/// @brief      SCR1 top testbench AXI
///

`include "scr1_arch_description.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_top_tb_axi (
`ifdef VERILATOR
    input logic clk
`endif // VERILATOR
);

//------------------------------------------------------------------------------
// Local parameters
//------------------------------------------------------------------------------
localparam                          SCR1_MEM_SIZE       = 1024*1024;
localparam                          TIMEOUT             = 'd2000_000;//20ms;
localparam                          ARCH                = 'h1;
localparam                          COMPLIANCE          = 'h2;
localparam                          ADDR_START          = 'h200;
localparam                          ADDR_TRAP_VECTOR    = 'h240;
localparam                          ADDR_TRAP_DEFAULT   = 'h1C0;

//------------------------------------------------------------------------------
// Local signal declaration
//------------------------------------------------------------------------------
logic                                   rst_n;
`ifndef VERILATOR
logic                                   clk         = 1'b0;
`endif // VERILATOR
logic                                   rtc_clk     = 1'b0;
logic   [31:0]                          fuse_mhartid;
integer                                 imem_req_ack_stall;
integer                                 dmem_req_ack_stall;
`ifdef SCR1_IPIC_EN
logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines;
`else // SCR1_IPIC_EN
logic                                   ext_irq;
`endif // SCR1_IPIC_EN
logic                                   soft_irq;

`ifdef SCR1_DBG_EN
logic                                   trst_n;
logic                                   tck;
logic                                   tms;
logic                                   tdi;
logic                                   tdo;
logic                                   tdo_en;
`endif // SCR1_DBG_EN

// Instruction Memory
logic [3:0]                             io_axi_imem_awid;
logic [31:0]                            io_axi_imem_awaddr;
logic [7:0]                             io_axi_imem_awlen;
logic [2:0]                             io_axi_imem_awsize;
logic [1:0]                             io_axi_imem_awburst;
logic                                   io_axi_imem_awlock;
logic [3:0]                             io_axi_imem_awcache;
logic [2:0]                             io_axi_imem_awprot;
logic [3:0]                             io_axi_imem_awregion;
logic [3:0]                             io_axi_imem_awuser;
logic [3:0]                             io_axi_imem_awqos;
logic                                   io_axi_imem_awvalid;
logic                                   io_axi_imem_awready;
logic [31:0]                            io_axi_imem_wdata;
logic [3:0]                             io_axi_imem_wstrb;
logic                                   io_axi_imem_wlast;
logic [3:0]                             io_axi_imem_wuser;
logic                                   io_axi_imem_wvalid;
logic                                   io_axi_imem_wready;
logic [3:0]                             io_axi_imem_bid;
logic [1:0]                             io_axi_imem_bresp;
logic                                   io_axi_imem_bvalid;
logic [3:0]                             io_axi_imem_buser;
logic                                   io_axi_imem_bready;
logic [3:0]                             io_axi_imem_arid;
logic [31:0]                            io_axi_imem_araddr;
logic [7:0]                             io_axi_imem_arlen;
logic [2:0]                             io_axi_imem_arsize;
logic [1:0]                             io_axi_imem_arburst;
logic                                   io_axi_imem_arlock;
logic [3:0]                             io_axi_imem_arcache;
logic [2:0]                             io_axi_imem_arprot;
logic [3:0]                             io_axi_imem_arregion;
logic [3:0]                             io_axi_imem_aruser;
logic [3:0]                             io_axi_imem_arqos;
logic                                   io_axi_imem_arvalid;
logic                                   io_axi_imem_arready;
logic [3:0]                             io_axi_imem_rid;
logic [31:0]                            io_axi_imem_rdata;
logic [1:0]                             io_axi_imem_rresp;
logic                                   io_axi_imem_rlast;
logic [3:0]                             io_axi_imem_ruser;
logic                                   io_axi_imem_rvalid;
logic                                   io_axi_imem_rready;

// Data Memory
logic [3:0]                             io_axi_dmem_awid;
logic [31:0]                            io_axi_dmem_awaddr;
logic [7:0]                             io_axi_dmem_awlen;
logic [2:0]                             io_axi_dmem_awsize;
logic [1:0]                             io_axi_dmem_awburst;
logic                                   io_axi_dmem_awlock;
logic [3:0]                             io_axi_dmem_awcache;
logic [2:0]                             io_axi_dmem_awprot;
logic [3:0]                             io_axi_dmem_awregion;
logic [3:0]                             io_axi_dmem_awuser;
logic [3:0]                             io_axi_dmem_awqos;
logic                                   io_axi_dmem_awvalid;
logic                                   io_axi_dmem_awready;
logic [31:0]                            io_axi_dmem_wdata;
logic [3:0]                             io_axi_dmem_wstrb;
logic                                   io_axi_dmem_wlast;
logic [3:0]                             io_axi_dmem_wuser;
logic                                   io_axi_dmem_wvalid;
logic                                   io_axi_dmem_wready;
logic [3:0]                             io_axi_dmem_bid;
logic [1:0]                             io_axi_dmem_bresp;
logic                                   io_axi_dmem_bvalid;
logic [3:0]                             io_axi_dmem_buser;
logic                                   io_axi_dmem_bready;
logic [3:0]                             io_axi_dmem_arid;
logic [31:0]                            io_axi_dmem_araddr;
logic [7:0]                             io_axi_dmem_arlen;
logic [2:0]                             io_axi_dmem_arsize;
logic [1:0]                             io_axi_dmem_arburst;
logic                                   io_axi_dmem_arlock;
logic [3:0]                             io_axi_dmem_arcache;
logic [2:0]                             io_axi_dmem_arprot;
logic [3:0]                             io_axi_dmem_arregion;
logic [3:0]                             io_axi_dmem_aruser;
logic [3:0]                             io_axi_dmem_arqos;
logic                                   io_axi_dmem_arvalid;
logic                                   io_axi_dmem_arready;
logic [3:0]                             io_axi_dmem_rid;
logic [31:0]                            io_axi_dmem_rdata;
logic [1:0]                             io_axi_dmem_rresp;
logic                                   io_axi_dmem_rlast;
logic [3:0]                             io_axi_dmem_ruser;
logic                                   io_axi_dmem_rvalid;
logic                                   io_axi_dmem_rready;

// Wathdogs
int unsigned                            watchdogs_cnt;

int unsigned                            f_results;
int unsigned                            f_info;
string                                  s_results;
string                                  s_info;
`ifdef SIGNATURE_OUT
string                                  s_testname;
bit                                     b_single_run_flag;
`endif  //  SIGNATURE_OUT
`ifdef VERILATOR
logic [255:0]                           test_file;
`else // VERILATOR
string                                  test_file;
`endif // VERILATOR

bit                                     test_running;
int unsigned                            tests_passed;
int unsigned                            tests_total;

bit [1:0]                               rst_cnt;
bit                                     rst_init;


`ifdef VERILATOR
function int identify_test (logic [255:0] testname);
    bit res;
    logic [79:0] pattern_compliance;
    logic [22:0] pattern_arch;
begin
    pattern_compliance = 80'h636f6d706c69616e6365; // compliance
    pattern_arch       = 'h61726368;             // arch
    res = 0;
    for (int i = 0; i<= 176; i++) begin
        if(testname[i+:80] == pattern_compliance) begin
            return COMPLIANCE;
        end
    end
    for (int i = 0; i<= 233; i++) begin
        if(testname[i+:23] == pattern_arch) begin
            return ARCH;
        end
    end
    `ifdef SIGNATURE_OUT
        return ~res;
    `else
        return res;
    `endif
end
endfunction : identify_test

function logic [255:0] get_filename (logic [255:0] testname);
logic [255:0] res;
int i, j;
begin
    testname[7:0] = 8'h66;
    testname[15:8] = 8'h6C;
    testname[23:16] = 8'h65;

    for (i = 0; i <= 248; i += 8) begin
        if (testname[i+:8] == 0) begin
            break;
        end
    end
    i -= 8;
    for (j = 255; i >= 0;i -= 8) begin
        res[j-:8] = testname[i+:8];
        j -= 8;
    end
    for (; j >= 0;j -= 8) begin
        res[j-:8] = 0;
    end

    return res;
end
endfunction : get_filename

function logic [255:0] get_ref_filename (logic [255:0] testname);
    logic [255:0] res;
    int i, j;
    logic [79:0] pattern_compliance;
    logic [22:0] pattern_arch;
    begin
        pattern_compliance = 80'h636f6d706c69616e6365; // compliance
        pattern_arch       = 'h61726368;             // arch

        for(int i = 0; i <= 176; i++) begin
            if(testname[i+:80] == pattern_compliance) begin
                testname[(i-8)+:88] = 0;
                break;
            end
        end

        for(int i = 0; i <= 233; i++) begin
            if(testname[i+:23] == pattern_arch) begin
                testname[(i-8)+:31] = 0;
                break;
            end
        end

        for(i = 32; i <= 248; i += 8) begin
            if(testname[i+:8] == 0) break;
        end
        i -= 8;
        for(j = 255; i > 24; i -= 8) begin
            res[j-:8] = testname[i+:8];
            j -= 8;
        end
        for(; j >=0;j -= 8) begin
            res[j-:8] = 0;
        end

        return res;
    end
    endfunction : get_ref_filename

function logic [2047:0] remove_trailing_whitespaces (logic [2047:0] str);
int i;
begin
    for (i = 0; i <= 2040; i += 8) begin
        if (str[i+:8] != 8'h20) begin
            break;
        end
    end
    str = str >> i;
    return str;
end
endfunction: remove_trailing_whitespaces

`else // VERILATOR
function int identify_test (string testname);
    begin
        if (testname.substr(0, 3) == "arch") begin
            return ARCH;
        end else if (testname.substr(0, 9) == "compliance") begin
            return COMPLIANCE;
        end else begin
            return 0;
        end
    end
endfunction : identify_test

function string get_filename (string testname);
        int length;
        begin
            length = testname.len();
            testname[length-1] = "f";
            testname[length-2] = "l";
            testname[length-3] = "e";

            return testname;
        end
endfunction : get_filename

function string get_ref_filename (string testname);
    begin
        if (identify_test(test_file) == COMPLIANCE) begin
            return testname.substr(11, testname.len() - 5);
        end else if (identify_test(test_file) == ARCH) begin
            return testname.substr(5, testname.len() - 5);
        end
    end
endfunction : get_ref_filename

`endif // VERILATOR

`ifndef VERILATOR
always #5   clk     = ~clk;         // 100 MHz
always #500 rtc_clk = ~rtc_clk;     // 1 MHz
`endif // VERILATOR

// Reset logic
assign rst_n = &rst_cnt;

always_ff @(posedge clk) begin
    if (rst_init)       rst_cnt <= '0;
    else if (~&rst_cnt) rst_cnt <= rst_cnt + 1'b1;
end


`ifdef SCR1_DBG_EN
initial begin
    trst_n  = 1'b0;
    tck     = 1'b0;
    tdi     = 1'b0;
    #900ns trst_n   = 1'b1;
    #500ns tms      = 1'b1;
    #800ns tms      = 1'b0;
    #500ns trst_n   = 1'b0;
    #100ns tms      = 1'b1;
end
`endif // SCR1_DBG_EN

//-------------------------------------------------------------------------------
// Run tests
//-------------------------------------------------------------------------------

`include "scr1_top_tb_runtests.sv"

//------------------------------------------------------------------------------
// Core instance
//------------------------------------------------------------------------------
scr1_top_axi i_top (
    // Reset
    .pwrup_rst_n            (rst_n                  ),
    .rst_n                  (rst_n                  ),
    .cpu_rst_n              (rst_n                  ),
`ifdef SCR1_DBG_EN
    .sys_rst_n_o            (                       ),
    .sys_rdc_qlfy_o         (                       ),
`endif // SCR1_DBG_EN

    // Clock
    .clk                    (clk                    ),
    .rtc_clk                (rtc_clk                ),

    // Fuses
    .fuse_mhartid           (fuse_mhartid           ),
`ifdef SCR1_DBG_EN
    .fuse_idcode            (`SCR1_TAP_IDCODE       ),
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    .irq_lines              (irq_lines              ),
`else // SCR1_IPIC_EN
    .ext_irq                (ext_irq                ),
`endif // SCR1_IPIC_EN
    .soft_irq               (soft_irq               ),

    // DFT
    .test_mode              (1'b0                   ),
    .test_rst_n             (1'b1                   ),

`ifdef SCR1_DBG_EN
    // JTAG
    .trst_n                 (trst_n                 ),
    .tck                    (tck                    ),
    .tms                    (tms                    ),
    .tdi                    (tdi                    ),
    .tdo                    (tdo                    ),
    .tdo_en                 (tdo_en                 ),
`endif // SCR1_DBG_EN

    // Instruction memory interface
    .io_axi_imem_awid       (io_axi_imem_awid       ),
    .io_axi_imem_awaddr     (io_axi_imem_awaddr     ),
    .io_axi_imem_awlen      (io_axi_imem_awlen      ),
    .io_axi_imem_awsize     (io_axi_imem_awsize     ),
    .io_axi_imem_awburst    (),
    .io_axi_imem_awlock     (),
    .io_axi_imem_awcache    (),
    .io_axi_imem_awprot     (),
    .io_axi_imem_awregion   (),
    .io_axi_imem_awuser     (),
    .io_axi_imem_awqos      (),
    .io_axi_imem_awvalid    (io_axi_imem_awvalid    ),
    .io_axi_imem_awready    (io_axi_imem_awready    ),
    .io_axi_imem_wdata      (io_axi_imem_wdata      ),
    .io_axi_imem_wstrb      (io_axi_imem_wstrb      ),
    .io_axi_imem_wlast      (io_axi_imem_wlast      ),
    .io_axi_imem_wuser      (),
    .io_axi_imem_wvalid     (io_axi_imem_wvalid     ),
    .io_axi_imem_wready     (io_axi_imem_wready     ),
    .io_axi_imem_bid        (io_axi_imem_bid        ),
    .io_axi_imem_bresp      (io_axi_imem_bresp      ),
    .io_axi_imem_bvalid     (io_axi_imem_bvalid     ),
    .io_axi_imem_buser      (4'd0                   ),
    .io_axi_imem_bready     (io_axi_imem_bready     ),
    .io_axi_imem_arid       (io_axi_imem_arid       ),
    .io_axi_imem_araddr     (io_axi_imem_araddr     ),
    .io_axi_imem_arlen      (io_axi_imem_arlen      ),
    .io_axi_imem_arsize     (io_axi_imem_arsize     ),
    .io_axi_imem_arburst    (io_axi_imem_arburst    ),
    .io_axi_imem_arlock     (),
    .io_axi_imem_arcache    (),
    .io_axi_imem_arprot     (),
    .io_axi_imem_arregion   (),
    .io_axi_imem_aruser     (),
    .io_axi_imem_arqos      (),
    .io_axi_imem_arvalid    (io_axi_imem_arvalid    ),
    .io_axi_imem_arready    (io_axi_imem_arready    ),
    .io_axi_imem_rid        (io_axi_imem_rid        ),
    .io_axi_imem_rdata      (io_axi_imem_rdata      ),
    .io_axi_imem_rresp      (io_axi_imem_rresp      ),
    .io_axi_imem_rlast      (io_axi_imem_rlast      ),
    .io_axi_imem_ruser      (4'd0                   ),
    .io_axi_imem_rvalid     (io_axi_imem_rvalid     ),
    .io_axi_imem_rready     (io_axi_imem_rready     ),

    // Data memory interface
    .io_axi_dmem_awid       (io_axi_dmem_awid       ),
    .io_axi_dmem_awaddr     (io_axi_dmem_awaddr     ),
    .io_axi_dmem_awlen      (io_axi_dmem_awlen      ),
    .io_axi_dmem_awsize     (io_axi_dmem_awsize     ),
    .io_axi_dmem_awburst    (),
    .io_axi_dmem_awlock     (),
    .io_axi_dmem_awcache    (),
    .io_axi_dmem_awprot     (),
    .io_axi_dmem_awregion   (),
    .io_axi_dmem_awuser     (),
    .io_axi_dmem_awqos      (),
    .io_axi_dmem_awvalid    (io_axi_dmem_awvalid    ),
    .io_axi_dmem_awready    (io_axi_dmem_awready    ),
    .io_axi_dmem_wdata      (io_axi_dmem_wdata      ),
    .io_axi_dmem_wstrb      (io_axi_dmem_wstrb      ),
    .io_axi_dmem_wlast      (io_axi_dmem_wlast      ),
    .io_axi_dmem_wuser      (),
    .io_axi_dmem_wvalid     (io_axi_dmem_wvalid     ),
    .io_axi_dmem_wready     (io_axi_dmem_wready     ),
    .io_axi_dmem_bid        (io_axi_dmem_bid        ),
    .io_axi_dmem_bresp      (io_axi_dmem_bresp      ),
    .io_axi_dmem_bvalid     (io_axi_dmem_bvalid     ),
    .io_axi_dmem_buser      (4'd0                   ),
    .io_axi_dmem_bready     (io_axi_dmem_bready     ),
    .io_axi_dmem_arid       (io_axi_dmem_arid       ),
    .io_axi_dmem_araddr     (io_axi_dmem_araddr     ),
    .io_axi_dmem_arlen      (io_axi_dmem_arlen      ),
    .io_axi_dmem_arsize     (io_axi_dmem_arsize     ),
    .io_axi_dmem_arburst    (io_axi_dmem_arburst    ),
    .io_axi_dmem_arlock     (),
    .io_axi_dmem_arcache    (),
    .io_axi_dmem_arprot     (),
    .io_axi_dmem_arregion   (),
    .io_axi_dmem_aruser     (),
    .io_axi_dmem_arqos      (),
    .io_axi_dmem_arvalid    (io_axi_dmem_arvalid    ),
    .io_axi_dmem_arready    (io_axi_dmem_arready    ),
    .io_axi_dmem_rid        (io_axi_dmem_rid        ),
    .io_axi_dmem_rdata      (io_axi_dmem_rdata      ),
    .io_axi_dmem_rresp      (io_axi_dmem_rresp      ),
    .io_axi_dmem_rlast      (io_axi_dmem_rlast      ),
    .io_axi_dmem_ruser      (4'd0                   ),
    .io_axi_dmem_rvalid     (io_axi_dmem_rvalid     ),
    .io_axi_dmem_rready     (io_axi_dmem_rready     )
);


//-------------------------------------------------------------------------------
// Memory instance
//-------------------------------------------------------------------------------
scr1_memory_tb_axi #(
    .SIZE    (SCR1_MEM_SIZE),
    .N_IF    (2            ),
    .W_ADR   (32           ),
    .W_DATA  (32           )
) i_memory_tb (
    // Common
    .rst_n          (rst_n),
    .clk            (clk),
`ifdef SCR1_IPIC_EN
    .irq_lines      (irq_lines),
`else // SCR1_IPIC_EN
    .ext_irq        (ext_irq),
`endif // SCR1_IPIC_EN
    .soft_irq       (soft_irq),

    // Write address channel
    .awid           ( {io_axi_imem_awid,   io_axi_dmem_awid}      ),
    .awaddr         ( {io_axi_imem_awaddr, io_axi_dmem_awaddr}    ),
    .awsize         ( {io_axi_imem_awsize, io_axi_dmem_awsize}    ),
    .awlen          ( {io_axi_imem_awlen,  io_axi_dmem_awlen}     ),
    .awvalid        ( {io_axi_imem_awvalid,io_axi_dmem_awvalid}   ),
    .awready        ( {io_axi_imem_awready,io_axi_dmem_awready}   ),

    // Write data channel
    .wdata          ( {io_axi_imem_wdata,  io_axi_dmem_wdata}     ),
    .wstrb          ( {io_axi_imem_wstrb,  io_axi_dmem_wstrb}     ),
    .wvalid         ( {io_axi_imem_wvalid, io_axi_dmem_wvalid}    ),
    .wlast          ( {io_axi_imem_wlast,  io_axi_dmem_wlast}     ),
    .wready         ( {io_axi_imem_wready, io_axi_dmem_wready}    ),

    // Write response channel
    .bready         ( {io_axi_imem_bready, io_axi_dmem_bready}    ),
    .bvalid         ( {io_axi_imem_bvalid, io_axi_dmem_bvalid}    ),
    .bid            ( {io_axi_imem_bid,    io_axi_dmem_bid}       ),
    .bresp          ( {io_axi_imem_bresp,  io_axi_dmem_bresp}     ),

    // Read address channel
    .arid           ( {io_axi_imem_arid,   io_axi_dmem_arid}      ),
    .araddr         ( {io_axi_imem_araddr, io_axi_dmem_araddr}    ),
    .arburst        ( {io_axi_imem_arburst,io_axi_dmem_arburst}   ),
    .arsize         ( {io_axi_imem_arsize, io_axi_dmem_arsize}    ),
    .arlen          ( {io_axi_imem_arlen,  io_axi_dmem_arlen}     ),
    .arvalid        ( {io_axi_imem_arvalid,io_axi_dmem_arvalid}   ),
    .arready        ( {io_axi_imem_arready,io_axi_dmem_arready}   ),

    // Read data channel
    .rvalid         ( {io_axi_imem_rvalid, io_axi_dmem_rvalid}    ),
    .rready         ( {io_axi_imem_rready, io_axi_dmem_rready}    ),
    .rid            ( {io_axi_imem_rid,    io_axi_dmem_rid}       ),
    .rdata          ( {io_axi_imem_rdata,  io_axi_dmem_rdata}     ),
    .rlast          ( {io_axi_imem_rlast,  io_axi_dmem_rlast}     ),
    .rresp          ( {io_axi_imem_rresp,  io_axi_dmem_rresp}     )
);

endmodule : scr1_top_tb_axi

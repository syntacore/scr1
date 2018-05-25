/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_top_tb_axi.sv>
/// @brief      SCR1 top testbench AXI
///

`include "scr1_arch_description.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_top_tb_axi ();

//------------------------------------------------------------------------------
// Local parameters
//------------------------------------------------------------------------------
localparam logic [`SCR1_XLEN-1:0]   SCR1_EXIT_ADDR      = 32'h000000F8;

//------------------------------------------------------------------------------
// Local signal declaration
//------------------------------------------------------------------------------
logic                                   rst_n;
logic                                   clk         = 1'b0;
logic                                   rtc_clk     = 1'b0;
logic   [31:0]                          fuse_mhartid;
integer                                 imem_req_ack_stall;
integer                                 dmem_req_ack_stall;
`ifdef SCR1_IPIC_EN
logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines;
`else // SCR1_IPIC_EN
logic                                   ext_irq     = 1'b0;
`endif // SCR1_IPIC_EN
logic                                   soft_irq    = 1'b0;

`ifdef SCR1_DBGC_EN
logic                                   trst_n;
logic                                   tck;
logic                                   tms;
logic                                   tdi;
logic                                   tdo;
logic                                   tdo_en;
`endif // SCR1_DBGC_EN

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

int unsigned                            f_results;
int unsigned                            f_info;
string                                  s_results;
string                                  s_info;

int unsigned                            tests_passed;
int unsigned                            tests_total;
int unsigned                            ret_val;

always #5   clk     = ~clk;     // 100 MHz
always #500 rtc_clk = ~rtc_clk; // 1 MHz

task reset();
    rst_n       = 0;
    #1 rst_n    = 1;
endtask

`ifdef SCR1_DBGC_EN
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
`endif // SCR1_DBGC_EN

//------------------------------------------------------------------------------
// Run tests
//------------------------------------------------------------------------------
initial begin
    $value$plusargs("imem_pattern=%h", imem_req_ack_stall);
    $value$plusargs("dmem_pattern=%h", dmem_req_ack_stall);
    $value$plusargs("test_info=%s", s_info);
    $value$plusargs("test_results=%s", s_results);

    fuse_mhartid        = 0;
    rst_n               = 1;

    f_info      = $fopen(s_info, "r");
    f_results   = $fopen(s_results, "a");

    forever begin
        if ($feof(f_info)) break;
        ret_val = $fscanf(f_info, "%s\n", i_memory_tb.stuff_file);
        i_top.i_core_top.i_pipe_top.i_tracelog.test_name = i_memory_tb.stuff_file;
        $write("\033[0;34m---Test: %s\033[0m\n", i_memory_tb.stuff_file);
        reset();
        forever begin
            @(posedge clk)
            if (i_top.i_core_top.i_pipe_top.curr_pc == SCR1_EXIT_ADDR) begin
                bit test_pass;

                test_pass =
                    (i_top.i_core_top.i_pipe_top.i_pipe_mprf.mprf_int[10] == 0);

                tests_total  += 1;
                tests_passed += test_pass;

                $fwrite( f_results,
                         "%s\t\t%s\n",
                         i_memory_tb.stuff_file,
                         (test_pass ? "PASS" : "__FAIL") );

                if (test_pass) $write("\033[0;32mTest passed\033[0m\n");
                else $write("\033[0;31mTest failed\033[0m\n");
                break;
            end
        end
    end
    $display("\n#--------------------------------------");
    $display("# Summary: %0d/%0d tests passed", tests_passed, tests_total);
    $display("#--------------------------------------\n");
    $fclose(f_info);
    $fclose(f_results);
    $finish();
end

//------------------------------------------------------------------------------
// Core instance
//------------------------------------------------------------------------------
scr1_top_axi i_top (
    // Control
    .rst_n                  (rst_n          ),
    .test_mode              ('0             ),
    .clk                    (clk            ),
    .rtc_clk                (rtc_clk        ),
    .rst_n_out              (               ),
    .fuse_mhartid           (fuse_mhartid   ),
`ifdef SCR1_IPIC_EN
    .irq_lines              (irq_lines      ),
`else // SCR1_IPIC_EN
    .ext_irq                (ext_irq        ),
`endif // SCR1_IPIC_EN
    .soft_irq               (soft_irq       ),
`ifdef SCR1_DBGC_EN
    .trst_n                 (trst_n         ),
    .tck                    (tck            ),
    .tms                    (tms            ),
    .tdi                    (tdi            ),
    .tdo                    (tdo            ),
    .tdo_en                 (tdo_en         ),
`endif // SCR1_DBGC_EN

    // Instruction memory
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

    // Data memory
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
    .SIZE    (1*1024*1024 ),
    .N_IF    (2           ),
    .W_ADR   (32          ),
    .W_DATA  (32          )

) i_memory_tb (

    // System
    .rst_n          (rst_n),
    .clk            (clk),
`ifdef SCR1_IPIC_EN
    .irq_lines      (irq_lines),
`endif // SCR1_IPIC_EN

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

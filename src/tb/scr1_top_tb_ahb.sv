/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_top_tb_ahb.sv>
/// @brief      SCR1 top testbench AHB
///

`include "scr1_arch_description.svh"
`include "scr1_ahb.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_top_tb_ahb (
`ifdef VERILATOR
    input logic clk
`endif // VERILATOR
);

//-------------------------------------------------------------------------------
// Local parameters
//-------------------------------------------------------------------------------
localparam                          SCR1_MEM_SIZE       = 1024*1024;
localparam                          TIMEOUT             = 'd2000_000;//20ms;
localparam                          ARCH                = 'h1;
localparam                          COMPLIANCE          = 'h2;
localparam                          ADDR_START          = 'h200;
localparam                          ADDR_TRAP_VECTOR    = 'h240;
localparam                          ADDR_TRAP_DEFAULT   = 'h1C0;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic                                   rst_n;
`ifndef VERILATOR
logic                                   clk         = 1'b0;
`endif // VERILATOR
logic                                   rtc_clk     = 1'b0;
`ifdef SCR1_IPIC_EN
logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines;
`else // SCR1_IPIC_EN
logic                                   ext_irq;
`endif // SCR1_IPIC_EN
logic                                   soft_irq;
logic [31:0]                            fuse_mhartid;
integer                                 imem_req_ack_stall;
integer                                 dmem_req_ack_stall;

logic                                   test_mode   = 1'b0;
`ifdef SCR1_DBG_EN
logic                                   trst_n;
logic                                   tck;
logic                                   tms;
logic                                   tdi;
logic                                   tdo;
logic                                   tdo_en;
`endif // SCR1_DBG_EN

// Instruction Memory Interface
logic   [3:0]                           imem_hprot;
logic   [2:0]                           imem_hburst;
logic   [2:0]                           imem_hsize;
logic   [1:0]                           imem_htrans;
logic   [SCR1_AHB_WIDTH-1:0]            imem_haddr;
logic                                   imem_hready;
logic   [SCR1_AHB_WIDTH-1:0]            imem_hrdata;
logic                                   imem_hresp;

// Memory Interface
logic   [3:0]                           dmem_hprot;
logic   [2:0]                           dmem_hburst;
logic   [2:0]                           dmem_hsize;
logic   [1:0]                           dmem_htrans;
logic   [SCR1_AHB_WIDTH-1:0]            dmem_haddr;
logic                                   dmem_hwrite;
logic   [SCR1_AHB_WIDTH-1:0]            dmem_hwdata;
logic                                   dmem_hready;
logic   [SCR1_AHB_WIDTH-1:0]            dmem_hrdata;
logic                                   dmem_hresp;

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
//-------------------------------------------------------------------------------
// Core instance
//-------------------------------------------------------------------------------
scr1_top_ahb i_top (
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

    // Instruction Memory Interface
    .imem_hprot         (imem_hprot     ),
    .imem_hburst        (imem_hburst    ),
    .imem_hsize         (imem_hsize     ),
    .imem_htrans        (imem_htrans    ),
    .imem_hmastlock     (),
    .imem_haddr         (imem_haddr     ),
    .imem_hready        (imem_hready    ),
    .imem_hrdata        (imem_hrdata    ),
    .imem_hresp         (imem_hresp     ),

    // Data Memory Interface
    .dmem_hprot         (dmem_hprot     ),
    .dmem_hburst        (dmem_hburst    ),
    .dmem_hsize         (dmem_hsize     ),
    .dmem_htrans        (dmem_htrans    ),
    .dmem_hmastlock     (),
    .dmem_haddr         (dmem_haddr     ),
    .dmem_hwrite        (dmem_hwrite    ),
    .dmem_hwdata        (dmem_hwdata    ),
    .dmem_hready        (dmem_hready    ),
    .dmem_hrdata        (dmem_hrdata    ),
    .dmem_hresp         (dmem_hresp     )
);

//-------------------------------------------------------------------------------
// Memory instance
//-------------------------------------------------------------------------------
scr1_memory_tb_ahb #(
    .SCR1_MEM_POWER_SIZE    ($clog2(SCR1_MEM_SIZE))
) i_memory_tb (
    // Control
    .rst_n                  (rst_n),
    .clk                    (clk),
`ifdef SCR1_IPIC_EN
    .irq_lines              (irq_lines),
`else // SCR1_IPIC_EN
    .ext_irq                (ext_irq),
`endif // SCR1_IPIC_EN
    .soft_irq               (soft_irq),
    .imem_req_ack_stall_in  (imem_req_ack_stall),
    .dmem_req_ack_stall_in  (dmem_req_ack_stall),

    // Instruction Memory Interface
    // .imem_hprot             (imem_hprot ),
    // .imem_hburst            (imem_hburst),
    .imem_hsize             (imem_hsize ),
    .imem_htrans            (imem_htrans),
    .imem_haddr             (imem_haddr ),
    .imem_hready            (imem_hready),
    .imem_hrdata            (imem_hrdata),
    .imem_hresp             (imem_hresp ),

    // Data Memory Interface
    // .dmem_hprot             (dmem_hprot ),
    // .dmem_hburst            (dmem_hburst),
    .dmem_hsize             (dmem_hsize ),
    .dmem_htrans            (dmem_htrans),
    .dmem_haddr             (dmem_haddr ),
    .dmem_hwrite            (dmem_hwrite),
    .dmem_hwdata            (dmem_hwdata),
    .dmem_hready            (dmem_hready),
    .dmem_hrdata            (dmem_hrdata),
    .dmem_hresp             (dmem_hresp )
);

endmodule : scr1_top_tb_ahb


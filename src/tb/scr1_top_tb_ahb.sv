/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
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
localparam logic [`SCR1_XLEN-1:0]   SCR1_EXIT_ADDR      = 32'h000000F8;

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
logic                                   ext_irq     = 1'b0;
`endif // SCR1_IPIC_EN
logic                                   soft_irq    = 1'b0;
logic [31:0]                            fuse_mhartid;
integer                                 imem_req_ack_stall;
integer                                 dmem_req_ack_stall;

logic                                   test_mode   = 1'b0;
`ifdef SCR1_DBGC_EN
logic                                   trst_n;
logic                                   tck;
logic                                   tms;
logic                                   tdi;
logic                                   tdo;
logic                                   tdo_en;
`endif // SCR1_DBGC_EN

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

int unsigned                            f_results;
int unsigned                            f_info;
string                                  s_results;
string                                  s_info;
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
function bit is_compliance (logic [255:0] testname);
    bit res;
    logic [79:0] pattern;
begin
    pattern = 80'h636f6d706c69616e6365; // compliance
    res = 0;
    for (int i = 0; i<= 176; i++) begin
        if(testname[i+:80] == pattern) begin
            return ~res;
        end
    end
    return res;
end
endfunction : is_compliance

function logic [255:0] get_filename (logic [255:0] testname);
logic [255:0] res;
int i, j;
begin
    testname[15:8] = 8'h66;
    testname[23:16] = 8'h6C;
    testname[31:24] = 8'h65;

    for (i = 0; i <= 248; i += 8) begin
        if (testname[i+:8] == 0) begin
            break;
        end
    end
    i -= 8;
    for (j = 255; i > 0;i -= 8) begin
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
logic [79:0] pattern;
begin
    pattern = 80'h636f6d706c69616e6365; // compliance

    for(int i = 0; i <= 176; i++) begin
        if(testname[i+:80] == pattern) begin
            testname[(i-8)+:88] = 0;
            break;
        end
    end

    for(i = 32; i <= 248; i += 8) begin
        if(testname[i+:8] == 0) break;
    end
    i -= 8;
    for(j = 255; i > 32;i -= 8) begin
        res[j-:8] = testname[i+:8];
        j -= 8;
    end
    for(; j >=0;j -= 8) begin
        res[j-:8] = 0;
    end

    return res;
end
endfunction : get_ref_filename

`else // VERILATOR
function bit is_compliance (string testname);
begin
    return (testname.substr(0, 9) == "compliance");
end
endfunction : is_compliance

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
    return testname.substr(11, testname.len() - 5);
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

//-------------------------------------------------------------------------------
// Run tests
//-------------------------------------------------------------------------------

initial begin
    $value$plusargs("imem_pattern=%h", imem_req_ack_stall);
    $value$plusargs("dmem_pattern=%h", dmem_req_ack_stall);
    $value$plusargs("test_info=%s", s_info);
    $value$plusargs("test_results=%s", s_results);

    fuse_mhartid = 0;

    f_info      = $fopen(s_info, "r");
    f_results   = $fopen(s_results, "a");
end

always_ff @(posedge clk) begin
    if (test_running) begin
        rst_init <= 1'b0;
        if ((i_top.i_core_top.i_pipe_top.curr_pc == SCR1_EXIT_ADDR) & ~rst_init & &rst_cnt) begin
        `ifdef VERILATOR
        logic [255:0] full_filename;
        full_filename = test_file;
        `else // VERILATOR
        string full_filename;
        full_filename = test_file;
        `endif // VERILATOR

            if (is_compliance(test_file)) begin
                bit test_pass;
                logic [31:0] tmpv, start, stop, ref_data, test_data;
                integer fd;
                `ifdef VERILATOR
                logic [2047:0] tmpstr;
                `else // VERILATOR
                string tmpstr;
                `endif // VERILATOR
                
                test_running <= 1'b0;
                test_pass = 1;

                $sformat(tmpstr, "riscv64-unknown-elf-readelf -s %s | grep 'begin_signature\\|end_signature' | awk '{print $2}' > elfinfo", get_filename(test_file));
                fd = $fopen("script.sh", "w");
                if (fd == 0) begin
                    $write("Can't open script.sh\n");
                    test_pass = 0;
                end
                $fwrite(fd, "%s", tmpstr);
                $fclose(fd);

                $system("sh script.sh");

                fd = $fopen("elfinfo", "r");
                if (fd == 0) begin
                    $write("Can't open elfinfo\n");
                    test_pass = 0;
                end
                if ($fscanf(fd,"%h\n%h", start, stop) != 2) begin
                    $write("Wrong elfinfo data\n");
                    test_pass = 0;
                end
                if (start > stop) begin
                    tmpv = start;
                    start = stop;
                    stop = tmpv;
                end
                $fclose(fd);

                $sformat(tmpstr, "riscv_compliance/ref_data/%s", get_ref_filename(test_file));
                fd = $fopen(tmpstr,"r");
                if (fd == 0) begin
                    $write("Can't open reference_data file: %s\n", tmpstr);
                    test_pass = 0;
                end
                while (!$feof(fd) && (start != stop)) begin
                    $fscanf(fd, "0x%h,\n", ref_data);
                    test_data = {i_memory_tb.memory[start+3], i_memory_tb.memory[start+2], i_memory_tb.memory[start+1], i_memory_tb.memory[start]};
                    test_pass &= (ref_data == test_data);
                    start += 4;
                end
                $fclose(fd);

                tests_total += 1;
                tests_passed += test_pass;
                $fwrite(f_results, "%s\t\t%s\n", test_file, (test_pass ? "PASS" : "__FAIL"));
                if (test_pass) begin
                    $write("\033[0;32mTest passed\033[0m\n");
                end else begin
                    $write("\033[0;31mTest failed\033[0m\n");
                end
            end else begin
                bit test_pass;
                test_running <= 1'b0;
                test_pass = (i_top.i_core_top.i_pipe_top.i_pipe_mprf.mprf_int[10] == 0);
                tests_total     += 1;
                tests_passed    += test_pass;
                $fwrite(f_results, "%s\t\t%s\n", test_file, (test_pass ? "PASS" : "__FAIL"));
                if (test_pass) begin
                    $write("\033[0;32mTest passed\033[0m\n");
                end else begin
                    $write("\033[0;31mTest failed\033[0m\n");
                end
            end
        end
    end else begin
`ifdef VERILATOR
        if ($fgets(test_file,f_info)) begin
`else // VERILATOR
        if (!$feof(f_info)) begin
            $fscanf(f_info, "%s\n", test_file);
`endif // VERILATOR
            // Launch new test
`ifdef SCR1_TRACE_LOG_EN
            i_top.i_core_top.i_pipe_top.i_tracelog.test_name = test_file;
`endif
            i_memory_tb.test_file = test_file;
            i_memory_tb.test_file_init = 1'b1;
            $write("\033[0;34m---Test: %s\033[0m\n", test_file);
            test_running <= 1'b1;
            rst_init <= 1'b1;
        end else begin
            // Exit
            $display("\n#--------------------------------------");
            $display("# Summary: %0d/%0d tests passed", tests_passed, tests_total);
            $display("#--------------------------------------\n");
            $fclose(f_info);
            $fclose(f_results);
            $finish();
        end
    end
end

//-------------------------------------------------------------------------------
// Core instance
//-------------------------------------------------------------------------------
scr1_top_ahb i_top (
    // Reset
    .pwrup_rst_n            (rst_n                  ),
    .rst_n                  (rst_n                  ),
    .cpu_rst_n              (rst_n                  ),
`ifdef SCR1_DBGC_EN
    .ndm_rst_n_out          (),
`endif // SCR1_DBGC_EN

    // Clock
    .clk                    (clk                    ),
    .rtc_clk                (rtc_clk                ),

    // Fuses
    .fuse_mhartid           (fuse_mhartid           ),
`ifdef SCR1_DBGC_EN
    .fuse_idcode            (`SCR1_TAP_IDCODE       ),
`endif // SCR1_DBGC_EN

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

`ifdef SCR1_DBGC_EN
    // JTAG
    .trst_n                 (trst_n                 ),
    .tck                    (tck                    ),
    .tms                    (tms                    ),
    .tdi                    (tdi                    ),
    .tdo                    (tdo                    ),
    .tdo_en                 (tdo_en                 ),
`endif // SCR1_DBGC_EN

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
`endif // SCR1_IPIC_EN
    .imem_req_ack_stall_in  (imem_req_ack_stall),
    .dmem_req_ack_stall_in  (dmem_req_ack_stall ),

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

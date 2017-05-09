/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_top_ahb.sv>
/// @brief      SCR1 AHB top
///

`include "scr1_arch_description.svh"
`include "scr1_memif.svh"
`include "scr1_ahb.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_top_ahb (
    // Control
    input   logic                                   rst_n,                  // Reset signal
    input   logic                                   test_mode,              // Test mode
    input   logic                                   clk,                    // System clock
    input   logic                                   rtc_clk,                // RTC clock
    output  logic                                   rst_n_out,              // Core reset from DBGC

    // Fuses
    input   logic [`SCR1_XLEN-1:0]                  fuse_mhartid,           // Hart ID

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines,              // IRQ
`else // SCR1_IPIC_EN
    input   logic                                   ext_irq,
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBGC_EN
    // -- JTAG I/F
    input   logic                                   trst_n,
    input   logic                                   tck,
    input   logic                                   tms,
    input   logic                                   tdi,
    output  logic                                   tdo,
    output  logic                                   tdo_en,
`endif // SCR1_DBGC_EN

    // Instruction Memory Interface
    output  logic [3:0]                             imem_hprot,
    output  logic [2:0]                             imem_hburst,
    output  logic [2:0]                             imem_hsize,
    output  logic [1:0]                             imem_htrans,
    output  logic                                   imem_hmastlock,
    output  logic [SCR1_AHB_WIDTH-1:0]              imem_haddr,
    input   logic                                   imem_hready,
    input   logic [SCR1_AHB_WIDTH-1:0]              imem_hrdata,
    input   logic                                   imem_hresp,

    // Data Memory Interface
    output  logic [3:0]                             dmem_hprot,
    output  logic [2:0]                             dmem_hburst,
    output  logic [2:0]                             dmem_hsize,
    output  logic [1:0]                             dmem_htrans,
    output  logic                                   dmem_hmastlock,
    output  logic [SCR1_AHB_WIDTH-1:0]              dmem_haddr,
    output  logic                                   dmem_hwrite,
    output  logic [SCR1_AHB_WIDTH-1:0]              dmem_hwdata,
    input   logic                                   dmem_hready,
    input   logic [SCR1_AHB_WIDTH-1:0]              dmem_hrdata,
    input   logic                                   dmem_hresp
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------

// Instruction memory interface from core to router
logic                                               core_imem_req_ack;
logic                                               core_imem_req;
type_scr1_mem_cmd_e                                 core_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       core_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       core_imem_rdata;
type_scr1_mem_resp_e                                core_imem_resp;

// Data memory interface from core to router
logic                                               core_dmem_req_ack;
logic                                               core_dmem_req;
type_scr1_mem_cmd_e                                 core_dmem_cmd;
type_scr1_mem_width_e                               core_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       core_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       core_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       core_dmem_rdata;
type_scr1_mem_resp_e                                core_dmem_resp;

// Instruction memory interface from router to TCM
logic                                               tcm_imem_req_ack;
logic                                               tcm_imem_req;
type_scr1_mem_cmd_e                                 tcm_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       tcm_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       tcm_imem_rdata;
type_scr1_mem_resp_e                                tcm_imem_resp;

// Data memory interface from router to TCM
logic                                               tcm_dmem_req_ack;
logic                                               tcm_dmem_req;
type_scr1_mem_cmd_e                                 tcm_dmem_cmd;
type_scr1_mem_width_e                               tcm_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       tcm_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       tcm_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       tcm_dmem_rdata;
type_scr1_mem_resp_e                                tcm_dmem_resp;

// Instruction memory interface from router to AHB bridge
logic                                               ahb_imem_req_ack;
logic                                               ahb_imem_req;
type_scr1_mem_cmd_e                                 ahb_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       ahb_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       ahb_imem_rdata;
type_scr1_mem_resp_e                                ahb_imem_resp;

// Data memory interface from router to AHB bridge
logic                                               ahb_dmem_req_ack;
logic                                               ahb_dmem_req;
type_scr1_mem_cmd_e                                 ahb_dmem_cmd;
type_scr1_mem_width_e                               ahb_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       ahb_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       ahb_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       ahb_dmem_rdata;
type_scr1_mem_resp_e                                ahb_dmem_resp;


//-------------------------------------------------------------------------------
// SCR1 core instance
//-------------------------------------------------------------------------------
scr1_core_top i_core_top (
    // Control
    .rst_n          (rst_n              ),
    .test_mode      (test_mode          ),
    .clk            (clk                ),
    .rtc_clk        (rtc_clk            ),
    .rst_n_out      (rst_n_out          ),
    .fuse_mhartid   (fuse_mhartid       ),
    // IRQ
`ifdef SCR1_IPIC_EN
    .irq_lines      (irq_lines          ),
`else // SCR1_IPIC_EN
    .ext_irq        (ext_irq            ),
`endif // SCR1_IPIC_EN
`ifdef SCR1_DBGC_EN
    // JTAG interface
    .trst_n         (trst_n             ),
    .tck            (tck                ),
    .tms            (tms                ),
    .tdi            (tdi                ),
    .tdo            (tdo                ),
    .tdo_en         (tdo_en             ),
`endif // SCR1_DBGC_EN
    // Instruction memory interface
    .imem_req_ack   (core_imem_req_ack  ),
    .imem_req       (core_imem_req      ),
    .imem_cmd       (core_imem_cmd      ),
    .imem_addr      (core_imem_addr     ),
    .imem_rdata     (core_imem_rdata    ),
    .imem_resp      (core_imem_resp     ),
    // Data memory interface
    .dmem_req_ack   (core_dmem_req_ack  ),
    .dmem_req       (core_dmem_req      ),
    .dmem_cmd       (core_dmem_cmd      ),
    .dmem_width     (core_dmem_width    ),
    .dmem_addr      (core_dmem_addr     ),
    .dmem_wdata     (core_dmem_wdata    ),
    .dmem_rdata     (core_dmem_rdata    ),
    .dmem_resp      (core_dmem_resp     )
);

//-------------------------------------------------------------------------------
// TCM instance
//-------------------------------------------------------------------------------
scr1_tcm #(
    .SCR1_TCM_SIZE  (`SCR1_DMEM_AWIDTH'h00010000)
) i_tcm (
    .clk            (clk                ),
    .rst_n          (rst_n_out          ),
    // Instruction interface to TCM
    .imem_req_ack   (tcm_imem_req_ack   ),
    .imem_req       (tcm_imem_req       ),
    .imem_cmd       (tcm_imem_cmd       ),
    .imem_addr      (tcm_imem_addr      ),
    .imem_rdata     (tcm_imem_rdata     ),
    .imem_resp      (tcm_imem_resp      ),
    // Data interface to TCM
    .dmem_req_ack   (tcm_dmem_req_ack   ),
    .dmem_req       (tcm_dmem_req       ),
    .dmem_cmd       (tcm_dmem_cmd       ),
    .dmem_width     (tcm_dmem_width     ),
    .dmem_addr      (tcm_dmem_addr      ),
    .dmem_wdata     (tcm_dmem_wdata     ),
    .dmem_rdata     (tcm_dmem_rdata     ),
    .dmem_resp      (tcm_dmem_resp      )
);

//-------------------------------------------------------------------------------
// Instruction memory router
//-------------------------------------------------------------------------------
scr1_imem_router #(
    .SCR1_ADDR_MASK     (`SCR1_IMEM_AWIDTH'hFFFF0000),
    .SCR1_ADDR_PATTERN  (`SCR1_IMEM_AWIDTH'h00480000)
) i_imem_router (
    .rst_n          (rst_n_out          ),
    .clk            (clk                ),
    // Interface to core
    .imem_req_ack   (core_imem_req_ack  ),
    .imem_req       (core_imem_req      ),
    .imem_cmd       (core_imem_cmd      ),
    .imem_addr      (core_imem_addr     ),
    .imem_rdata     (core_imem_rdata    ),
    .imem_resp      (core_imem_resp     ),
    // Interface to AHB bridge
    .port0_req_ack  (ahb_imem_req_ack   ),
    .port0_req      (ahb_imem_req       ),
    .port0_cmd      (ahb_imem_cmd       ),
    .port0_addr     (ahb_imem_addr      ),
    .port0_rdata    (ahb_imem_rdata     ),
    .port0_resp     (ahb_imem_resp      ),
    // Interface to TCM
    .port1_req_ack  (tcm_imem_req_ack   ),
    .port1_req      (tcm_imem_req       ),
    .port1_cmd      (tcm_imem_cmd       ),
    .port1_addr     (tcm_imem_addr      ),
    .port1_rdata    (tcm_imem_rdata     ),
    .port1_resp     (tcm_imem_resp      )
);

//-------------------------------------------------------------------------------
// Data memory router
//-------------------------------------------------------------------------------
scr1_dmem_router #(
    .SCR1_ADDR_MASK     (`SCR1_DMEM_AWIDTH'hFFFF0000),
    .SCR1_ADDR_PATTERN  (`SCR1_DMEM_AWIDTH'h00480000)
) i_dmem_router (
    .rst_n          (rst_n_out          ),
    .clk            (clk                ),
    // Interface to core
    .dmem_req_ack   (core_dmem_req_ack  ),
    .dmem_req       (core_dmem_req      ),
    .dmem_cmd       (core_dmem_cmd      ),
    .dmem_width     (core_dmem_width    ),
    .dmem_addr      (core_dmem_addr     ),
    .dmem_wdata     (core_dmem_wdata    ),
    .dmem_rdata     (core_dmem_rdata    ),
    .dmem_resp      (core_dmem_resp     ),
    // Interface to AHB bridge
    .port0_req_ack  (ahb_dmem_req_ack   ),
    .port0_req      (ahb_dmem_req       ),
    .port0_cmd      (ahb_dmem_cmd       ),
    .port0_width    (ahb_dmem_width     ),
    .port0_addr     (ahb_dmem_addr      ),
    .port0_wdata    (ahb_dmem_wdata     ),
    .port0_rdata    (ahb_dmem_rdata     ),
    .port0_resp     (ahb_dmem_resp      ),
    // Interface to TCM
    .port1_req_ack  (tcm_dmem_req_ack   ),
    .port1_req      (tcm_dmem_req       ),
    .port1_cmd      (tcm_dmem_cmd       ),
    .port1_width    (tcm_dmem_width     ),
    .port1_addr     (tcm_dmem_addr      ),
    .port1_wdata    (tcm_dmem_wdata     ),
    .port1_rdata    (tcm_dmem_rdata     ),
    .port1_resp     (tcm_dmem_resp      )
);

//-------------------------------------------------------------------------------
// Instruction memory AHB bridge
//-------------------------------------------------------------------------------
scr1_imem_ahb i_imem_ahb (
    .rst_n          (rst_n_out          ),
    .clk            (clk                ),
    // Interface to imem router
    .imem_req_ack   (ahb_imem_req_ack   ),
    .imem_req       (ahb_imem_req       ),
    .imem_cmd       (ahb_imem_cmd       ),
    .imem_addr      (ahb_imem_addr      ),
    .imem_rdata     (ahb_imem_rdata     ),
    .imem_resp      (ahb_imem_resp      ),
    // AHB interface
    .hprot          (imem_hprot         ),
    .hburst         (imem_hburst        ),
    .hsize          (imem_hsize         ),
    .htrans         (imem_htrans        ),
    .hmastlock      (imem_hmastlock     ),
    .haddr          (imem_haddr         ),
    .hready         (imem_hready        ),
    .hrdata         (imem_hrdata        ),
    .hresp          (imem_hresp         )
);

//-------------------------------------------------------------------------------
// Data memory AHB bridge
//-------------------------------------------------------------------------------
scr1_dmem_ahb i_dmem_ahb (
    .rst_n          (rst_n_out          ),
    .clk            (clk                ),
    // Interface to dmem router
    .dmem_req_ack   (ahb_dmem_req_ack   ),
    .dmem_req       (ahb_dmem_req       ),
    .dmem_cmd       (ahb_dmem_cmd       ),
    .dmem_width     (ahb_dmem_width     ),
    .dmem_addr      (ahb_dmem_addr      ),
    .dmem_wdata     (ahb_dmem_wdata     ),
    .dmem_rdata     (ahb_dmem_rdata     ),
    .dmem_resp      (ahb_dmem_resp      ),
    // AHB interface
    .hprot          (dmem_hprot         ),
    .hburst         (dmem_hburst        ),
    .hsize          (dmem_hsize         ),
    .htrans         (dmem_htrans        ),
    .hmastlock      (dmem_hmastlock     ),
    .haddr          (dmem_haddr         ),
    .hwrite         (dmem_hwrite        ),
    .hwdata         (dmem_hwdata        ),
    .hready         (dmem_hready        ),
    .hrdata         (dmem_hrdata        ),
    .hresp          (dmem_hresp         )
);

endmodule : scr1_top_ahb



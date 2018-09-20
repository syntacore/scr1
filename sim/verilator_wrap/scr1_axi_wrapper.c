
#include <stdio.h>
#include <verilated.h>
#include "Vscr1_top_tb_axi.h"

Vscr1_top_tb_axi *top;

vluint64_t main_time = 0;

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    top = new Vscr1_top_tb_axi;

    while (!Verilated::gotFinish()) {
        if ((main_time % 10) == 1) {
            top->clk = 1;
        }
        if ((main_time % 10) == 6) {
            top->clk = 0;
        }
        top->eval();
        main_time++;
    }
    top->final();
    delete top;
}
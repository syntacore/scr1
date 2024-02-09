#include "sc_print.h"
#include "csr.h"

#define mstatush 0x310

int main()
{
    sc_printf("initial value of mstatush: %d\n", read_csr(mstatush));
    write_csr(mstatush,0xffffffff);
    sc_printf("value of mstatush after trying to write $ffffffff: %d\n", read_csr(mstatush));
    return 0;
}

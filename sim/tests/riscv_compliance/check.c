#include "stdint.h"

int check(void)
{    
    static const uint32_t ref[] = {
#include ""
                     };

    extern uint32_t begin_signature;
    const uint32_t *my_res = &begin_signature;
    int i;
    
    for (i = 0; i < sizeof(ref)/sizeof(*ref); i++) {
        if (my_res[i] != ref[i]) {
            return -1;
        }
    }
    return 0;
}
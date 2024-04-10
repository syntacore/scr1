#include "sc_print.h"
#include "csr.h"

#define mstatush 0x310
#define configure_big_endian set_csr(mstatush, 1<<5)
#define configure_little_endian clear_csr(mstatush, 1<<5)

int test_instruction(char* name,uint32_t result,uint32_t expected)
{
  sc_printf("testing instruccion %s. result:%#08x expected:%#08x.",name, result, expected);
  if(result==expected)
    {sc_printf("\n");return 0;}
  //else
  sc_printf("    FAILS\n");
  return 1;
}

void simulate_little_endian_store(unsigned int size, uint32_t value, void* address, int offset)
{
  for(int i=offset;i<size+offset;i++)
  {
    *( ((uint8_t*)address) +i) = (uint8_t)value;
    value>>=8;
  }
}

void simulate_big_endian_store(unsigned int size, uint32_t value, void* address, int offset)
{
  for(int i=size+offset-1;i>=offset;i--)
  {
    *( ((uint8_t*)address) +i) = (uint8_t)value;
    value>>=8;
  }
}

uint32_t simulate_little_endian_load(unsigned int size, int is_signed, void* address, int offset)
{
  uint8_t byte;
  uint32_t value=0;
  uint8_t* storedp=(uint8_t*)address+offset+size-1;
  for(int i=0;i<size;i++)
  {
    value<<=8;
    byte=*(storedp--);
    value+=byte;
  }
  if( size<4 && is_signed &&  (byte & (1<<7)))
    value |= (-1<<(size<<3));
  return value;
}

uint32_t simulate_big_endian_load(unsigned int size, int is_signed, void* address, int offset)
{
  uint8_t byte;
  uint32_t value=0;
  uint8_t* storedp=(uint8_t*)address+offset;
  for(int i=0;i<size;i++)
  {
    value<<=8;
    byte=*(storedp++);
    value+=byte;
  }
  if( size<4 && is_signed &&  (byte & (1<<7)))
    value |= (-1<<(size<<3));
  return value;
}

uint32_t big_endian_LW(void* address, int offset)
{
    uint32_t value;
    volatile uint32_t* efective_address= (uint32_t*) (address+offset);
    configure_big_endian;
    value=*efective_address;
    configure_little_endian;
    return value;
}

uint32_t big_endian_LHU(void* address, int offset)
{
    uint32_t value;
    volatile uint16_t* efective_address= (uint16_t*) (address+offset);
    configure_big_endian;
    value=*efective_address;
    configure_little_endian;
    return value;
}

uint32_t big_endian_LH(void* address, int offset)
{
    int32_t value;
    volatile int16_t* efective_address= (int16_t*) (address+offset);
    configure_big_endian;
    value=*efective_address;
    configure_little_endian;
    return value;
}

uint32_t big_endian_LBU(void* address, int offset)
{
    uint32_t value;
    volatile uint8_t* efective_address= (uint8_t*) (address+offset);
    configure_big_endian;
    value=*efective_address;
    configure_little_endian;
    return value;
}

uint32_t big_endian_LB(void* address, int offset)
{
    int32_t value;
    volatile int8_t* efective_address= (int8_t*) (address+offset);
    configure_big_endian;
    value=*efective_address;
    configure_little_endian;
    return value;
}

void big_endian_SW(uint32_t value, void* address, int offset)
{
    volatile uint32_t* efective_address= (uint32_t*) (address+offset);
    configure_big_endian;
    *efective_address=value;
    configure_little_endian;
}

void big_endian_SH(uint32_t value, void* address, int offset)
{
    volatile uint16_t* efective_address= (uint16_t*) (address+offset);
    configure_big_endian;
    *efective_address=value;
    configure_little_endian;
}

void big_endian_SB(uint32_t value, void* address, int offset)
{
    volatile uint8_t* efective_address= (uint8_t*) (address+offset);
    configure_big_endian;
    *efective_address=value;
    configure_little_endian;
}

int main()
{
  int fails=0;
  int size,logsize,offset,is_signed;
  uint32_t stored=0x5678abcd;
  uint32_t result,expected;
  char* instruction_name;

  sc_printf("\nTesting big endian data access\n\n");

  for(logsize=0;logsize<3;logsize++)
  {
    size=1<<logsize;
    for(offset=0;offset<4;offset+=size)
    {
      for(is_signed=0;is_signed<2 && !(logsize==2 && is_signed);is_signed++)
      {
          expected=simulate_big_endian_load(size,is_signed,&stored,offset);
          switch (logsize)
          {
            case 0:
              result= is_signed? big_endian_LB(&stored,offset) : big_endian_LBU(&stored,offset);
              instruction_name= is_signed? " LB" : "LBU";
              break;
            case 1:
              result= is_signed? big_endian_LH(&stored,offset) : big_endian_LHU(&stored,offset);
              instruction_name= is_signed? " LH" : "LHU";
              break;
            case 2:
              result= big_endian_LW(&stored,offset);
              instruction_name= " LW";
              break;
          }
      fails|=test_instruction(instruction_name,result,expected);
      }
    }
  }

  for(logsize=0;logsize<3;logsize++)
  {
    size=1<<logsize;
    for(offset=0;offset<4;offset+=size)
    {
      result=0x12345678;
      expected=0x12345678;
      simulate_big_endian_store(size, 0x5678abcd, &expected, offset);
      switch (logsize) {
        case 0:
          big_endian_SB(0x5678abcd,&result,offset);
          instruction_name="SB";
          break;
        case 1:
          big_endian_SH(0x5678abcd,&result,offset);
          instruction_name="SH";
          break;
        case 2:
          big_endian_SW(0x5678abcd,&result,offset);
          instruction_name="SW";
          break;
      }
      fails|=test_instruction(instruction_name,result,expected);
    }
  }

  sc_printf("\nTesting little endian data access\n\n");

  for(logsize=0;logsize<3;logsize++)
  {
    size=1<<logsize;
    for(offset=0;offset<4;offset+=size)
    {
      for(is_signed=0;is_signed<2 && !(logsize==2 && is_signed);is_signed++)
      {
          expected=simulate_little_endian_load(size,is_signed,&stored,offset);
          switch (logsize)
          {
            case 0:
              result= is_signed? *(int8_t*)(((void*) &stored)+offset) : *(uint8_t*)(((void*) &stored)+offset);
              instruction_name= is_signed? " LB" : "LBU";
              break;
            case 1:
              result= is_signed? *(int16_t*)(((void*) &stored)+offset) : *(uint16_t*)(((void*) &stored)+offset);
              instruction_name= is_signed? " LH" : "LHU";
              break;
            case 2:
              result= stored;
              instruction_name= " LW";
              break;
          }
      fails|=test_instruction(instruction_name,result,expected);
      }
    }
  }

  for(logsize=0;logsize<3;logsize++)
  {
    size=1<<logsize;
    for(offset=0;offset<4;offset+=size)
    {
      result=0x12345678;
      expected=0x12345678;
      simulate_little_endian_store(size, 0x5678abcd, &expected, offset);
      switch (logsize) {
        case 0:
          *(int8_t*)(((void*) &result)+offset)=0x5678abcd;
          instruction_name="SB";
          break;
        case 1:
          *(int16_t*)(((void*) &result)+offset)=0x5678abcd;
          instruction_name="SH";
          break;
        case 2:
          result=0x5678abcd;
          instruction_name="SW";
          break;
      }
      fails|=test_instruction(instruction_name,result,expected);
    }
  }

  return fails;
}

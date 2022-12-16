# Лабораторная работа 2. Симуляция SCR1

## Постановка задачи
Обработать исключение IllegalInstruction выводом строки "incorrect instruction". Настроить ресет вектор и вектор обработки прерываний на 0xF00 и 0xB00 соответственно. Проверить работу программы на примере isa/rv32mi/illegal.S.

## Последовательнось действий для выполнения ЛР

~~~bash
cd <WORK_LIB>
git clone https://github.com/quangmta/scr1 # клонирование 
cd ./scr1 # переходим в папку с проектом
git submodule update --init --recursive # обновляем сабрепо с тестами
git checkout -b lab_scr1_sim # создаем ветку для выполнения лабораторной и переходим в нее

code . # Выполняем лабораторную работу в visual studio code

git add . # индексируем все измения
git commit -am "add lab" # создаем коммит
git push origin lab_scr1_sim # пушим коммит на сервер
~~~

В Visual Studio Code делаем следующее:

* Создаем дирректорию lab_scr1_sim и файл README.md в ней. В файле описываем поставленную задачу.
* Модифицируем список тестов в файле .../scr1/sim/tests/riscv_isa/rv32_tests.inc
* В терминале прописываем путь до тулчейна (сv лаб 1) _PATH=.../riscv-tools/riscv-gcc-10.2.0-gbbc9263-210318T1412/bin:$PATH_
* Пробуем запустить симуляцию: _make TARGETS="riscv_isa"_
* Модифицируем вектора прирываний и ресетов в процессоре. _/scr1/src/includes/scr1_arch_description.svh_ меняем _SCR1_ARCH_RST_VECTOR_ и _SCR1_ARCH_MTVEC_BASE_
* Модифицируем скрипты линковщика для правильной сборки проекта.
    * Для этого заходим в файл sim/tests/common/link.ld и корректируем в нем смещение кода
    * в файле sim/tests/common/riscv_macros.h также корректируем смещение
    * в случае, если направильно настроили, то тест перестанет проходить. Для отладки полезно открывать dump и в нем смотреть адреса, по которым расположено начало программа и trap вектор scr1/build/verilator_AHB_MAX_imc_IPIC_1_TCM_1_VIRQ_1_TRACE_0/illegal.dump
    * **Между перезапусками не забываем выполнять make clean**
* После того, как правильно настроили вектора модифицируем обработчик прерывания

После завершения работы необходимо установить _sudo apt install gtkwave_. Собрать проект в режиме генерации wave форм: _make run_verilator_wf TARGETS="riscv_isa"_. После этого можно открыть wave форму в дирректории _scr1/build/verilator_wf_AHB_MAX_imc_IPIC_1_TCM_1_VIRQ_1_TRACE_1 командой  _gtkwave ./simx.vcd_
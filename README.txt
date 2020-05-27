Design and verification of AXI4 Lite Bus

README FILE:
----------------------------------------------------------------------------------------------
axi4_lite_Defs.sv - Contains the global definitions such as parameters for the AXI4 Lite bus.

axi4_lite_if.sv - Interface for AXI4 Lite Bus and defines the interface between master and 
slave of the AXI4 Lite bus.

axi4_lite_master.sv - Contains a master module which initiates the read and write operations.
Implemented two FSMs for read and write operation and each one has four states to traverse through
the sequence of steps to complete the transaction.

axi4_lite_slave.sv - Slave module for AXI4 Lite Bus.Contains a slave module which is driven by the 
master for the read and write operations.Implemented two FSMs for read and write operation and each
one has four states to traverse through the sequence of steps to complete the transaction.

read_address_tb.sv - Read Address Channel Testbench.Implements a testbench for read address channel 
of AXI4 Lite bus.Assertions are run along with the testcase to verify the functionality of the read 
address channel.

read_data_tb.sv - Read Data Channel Testbench.Implements a testbench for read data channel of AXI4 
Lite bus.Assertions are run along with the testcase to verify the functionality of the read data 
channel.

write_address_tb.sv - Write Address Channel Testbench.Implements a testbench for write address 
channel of AXI4 Lite bus.Assertions are run along with the testcase to verify the functionality of 
the write address channel.

write_data_tb.sv - Write Data Channel Testbench.Implements a testbench for write data channel of 
AXI4 Lite bus.Assertions are run along with the testcase to verify the functionality of the write 
data channel.

write_response_tb.sv - Write Response Channel Testbench.Implements a testbench for write response 
channel of AXI4 Lite bus.Assertions are run along with the testcase to verify the functionality of 
the write response channel.

Top.sv: Top module  drives the inputs to the master to perform read and write operations.This contains
several test cases to verify the functionality of the AXI4 Lite bus.

Top_with_assertions.sv: This file includes assertions for state transitions for the read and write FSMs
of both master and slave that run along with the top testbench module.




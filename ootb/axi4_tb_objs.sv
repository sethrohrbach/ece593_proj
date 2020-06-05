////////////////////////////////////////////////////////////////
// axi4_tb_objs.sv - object definitions for an AXI4-Lite bus testbench.
//
// Author: Seth Rohrbach (rseth@pdx.edu), Sumeet S. Pawar (pawar@pdx.edu), Surakshith Reddy Mothe (smothe@pdx.edu)
// Modified: June 2, 2020
//
// Description:
// ------------
// Objects to be used by an object oriented test bench for the AXI4-Lite bus.
// Implements direct and random testcases which can be called in the environment class.
////////////////////////////////////////////////////////////////

import axi4_lite_Defs::*;

class axi4_tester;

  //Hook the tester up with the AXI4:
  virtual axi4_lite_bfm bfm;

  //To store values for comparison:
  logic [Data_Width-1:0] local_mem[4096];

  int i;


  //TB local vars:
  bit wr_en = 0;
  bit rd_en = 0;
  bit clk = 0;

  function new (virtual axi4_lite_bfm b);
    bfm = b;
    for (i = 0; i < 4096; i++) begin
      local_mem[i] = 0;
    end
  endfunction: new

//Generate a random address:
  protected function logic gen_addr();
  logic [Addr_Width-1:0] addr = $random;
  return addr;
  endfunction : gen_addr

//Generate a random write value:
  protected function logic gen_data();
  logic [Data_Width-1:0] data = $random;
  return data;
  endfunction : gen_data

  //Write a value out to the light bus and also to local mem.
  protected task rand_write_op();
  //@(posedge clk);
  logic [Addr_Width-1:0] Write_Address = gen_addr();
  logic [Data_Width-1:0] Write_Data = gen_data();
  bfm.WVALID = 1;
  bfm.AWVALID = 1;
  bfm.AWADDR = Write_Address;
  bfm.WDATA = Write_Data;
  repeat(5) @(posedge clk);
  bfm.WVALID = 0;
  bfm.AWVALID = 0;
  endtask: rand_write_op

  protected task rand_read_op();
  //@(posedge clk);
  logic [Addr_Width-1:0] Read_Address = gen_addr();

  bfm.ARVALID = 1;
  local_mem[Read_Address] = bfm.RDATA;
  repeat(5) @(posedge clk);
  bfm.ARVALID = 0;
  endtask : rand_read_op

  //Let there be clock!
  /*
  initial begin
    forever #(10 / 2) clk = ~clk;
  end
  */

  protected task execute();
  int i = 0;
  for (i = 0; i < 4096; i++) begin
    @(posedge clk);
    fork
    rand_write_op();
    rand_read_op();
    join
  end
endtask : execute

endclass: axi4_tester


/*
// Randomization class that is derieved from axi4_tester class
class Randomization extends axi4_tester;

  rand Read_Address;	// Declaring Read Address to be of rand type
  rand Write_Address;	// Declaring Write Address to be of rand type
  rand Write_Data;		// Declaring Write Data to be of rand type
  rand rd_en;			// Declaring Read Enable to be of rand type
  rand wr_en;			// Declaring Write Enable to be of rand type
  rand addr_rand[10];	// Declaring an array of 10 elements to be of rand type
  bit temp_en;			// A bit to temporarily hold the previous enable signal

// ------------------------------------------ RESET TASK ------------------------------------------
  // Declaring a reset task; ARESETN is is an active low signal
  task Reset();
    @(posedge ACLK);        // Waiting for 1 clock before we provide ARESETN(Reset signal)
    $display("RESET STARTED");
    ARESETN = 0;          // Providing ARESETN(Reset signal)
    repeat (5) @(posedge ACLK);   // Waiting 5 clocks
    ARESETN = 1;          // De-asserting the ARESETN(Reset signal)
    $display("RESET ENDED");    // Reset operation completed
    @(posedge ACLK);
  endtask : Reset

// ------------------------------------------ READ TASK ------------------------------------------
  task Readtask(input [Addr_Width-1:0] R_Address);
    wr_en = 0;            // Setting Write enable to 0
    rd_en = 1;            // Setting Read enable to 1
    Read_Address = R_Address;   // Providing Read Address to the DUT
    repeat(5) @(posedge ACLK);    // Waiting for 5 clocks for the Read task to complete
    $display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, bfm.ARADDR, bfm.RDATA, slave.mem[Read_Address]);
  endtask : Readtask

// ------------------------------------------ WRITE TASK ------------------------------------------
  task Writetask(input [Addr_Width-1:0] W_Address, input [Data_Width-1:0] W_Data);
    rd_en = 0;            // Setting Read enable to 0
    wr_en = 1;            // Setting Write enable to 1
    Write_Address = W_Address;    // Providing the Write Address to the DUT
    Write_Data = W_Data;      // Providing the Write Data to the DUT
    repeat(5) @(posedge ACLK);    // Waiting for 5 clocks for the Write task to complete
    $display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, slave.mem[Write_Address]);
  endtask : Writetask


// ------------------------------------------ TESTCASES TASKS ------------------------------------------
// ------------------------- Single Write followed by a single Read to the same intermediate location -------------------------
  task Write_Read_IntermediateLocation_Test();
    Reset();                           // Calling Reset task
    Writetask(32'h101, 32'hFFFFFFF0);  // Calling Write task
    Readtask(32'h101);                 // Calling Read task
  endtask : Write_Read_IntermediateLocation_Test

// ------------------------- Single Write followed by a single Read to the same first location -------------------------
  task Write_Read_FirstLocation_Test();
    Reset();                           // Calling Reset task
    Writetask(32'h000, 32'hFFFFFFF0);  // Calling Write task
    Readtask(32'h000);                 // Calling Read task
  endtask : Write_Read_FirstLocation_Test

// ------------------------- Single Write followed by a single Read to the same last location -------------------------
  task Write_Read_LastLocation_Test();
    Reset();                           // Calling Reset task
    Writetask(32'h111, 32'hFFFFFFF0);  // Calling Write task
    Readtask(32'h111);                 // Calling Read task
  endtask : Write_Read_LastLocation_Test

// ------------------------- Perform single Read and a single Write at the same time to the same location -------------------------
task Write_Read_Sametime_SameLocation_Test();
    rd_en = 1;            				// Setting Read enable to 1
    wr_en = 1;            				// Setting Write enable to 1
    Write_Address = 32'h101;    		// Providing the Write Address to the DUT
    Write_Data = 32'hFFFFFFF0;      	// Providing the Write Data to the DUT
    Read_Address = 32'h101;   			// Providing Read Address to the DUT
    repeat(10) @(posedge ACLK);    		// Waiting for 10 clocks to ensure both Read and Write tasks have been completed
    $display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, bfm.ARADDR, bfm.RDATA, slave.mem[Read_Address]);
    $display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, slave.mem[Write_Address]);
  endtask : Write_Read_Sametime_SameLocation_Test

// ------------------------- Perform single Read and a single Write at the same time to a different location -------------------------
  task Write_Read_Sametime_DifferentLocation_Test();
    rd_en = 1;            				// Setting Read enable to 1
    wr_en = 1;            				// Setting Write enable to 1
    Write_Address = 32'h101;    		// Providing the Write Address to the DUT
    Write_Data = 32'hFFFFFFF0;      	// Providing the Write Data to the DUT
    Read_Address = 32'h100;   			// Providing Read Address to the DUT
    repeat(10) @(posedge ACLK);    		// Waiting for 10 clocks to ensure both Read and Write tasks have been completed
    $display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, bfm.ARADDR, bfm.RDATA, slave.mem[Read_Address]);
    $display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, slave.mem[Write_Address]);
  endtask : Write_Read_Sametime_DifferentLocation_Test

// ------------------------- Perform Writes first to all consecutive locations followed by Reads later to the same consecutive locations -------------------------
  task Multiple_Writes_Multiple_Reads_ConsecutiveLocations_Test();
    int i;							    // Declaring a local variable 'i' for the for loop
    int j;								// Declaring a local variable 'j' for the for loop
    Reset();                            // Calling Reset task

    for (i = 0; i < 4096; i++) begin    // Loop to iterate through all locations
      Writetask(i, i);  				// Calling Write task
    end

    for (j = 0; j < 4096; j++) begin	// Loop to iterate through all locations
      Readtask(j);                 		// Calling Read task
    end
  endtask : Multiple_Writes_Multiple_Reads_ConsecutiveLocations_Test

// ------------------------- Perform Writes first to all non-consecutive locations followed by Reads later to the same non-consecutive locations -------------------------
  task Multiple_Writes_Multiple_Reads_RandomLocations_Test();
    int i;								// Declaring a local variable 'i' for the for loop
    int j;								// Declaring a local variable 'j' for the for loop
    Reset();                            // Calling Reset task

    for (i = 0; i < 4096; i = i+4) begin // Loop to iterate through random locations throughout the memory size
      Writetask(i, i);  				 // Calling Write task
    end

    for (j = 0; j < 4096; j = j+4) begin // Loop to iterate through random locations throughout the memory size
      Readtask(j);                 		 // Calling Read task
    end
  endtask : Multiple_Writes_Multiple_Reads_RandomLocations_Test

// ------------------------- Perform Overwriting at the same location followed by a single Read to the same location -------------------------
  task Multiple_Writes_Single_Read_SameLocation_Test();
    int i;								// Declaring a local variable 'i' for the for loop
      Reset();                          // Calling Reset task

    for (i = 0; i < 40; i++) begin		// Loop to iterate
      Writetask(32'h011, i);            // Calling Write task while keeping the Write Address same and changing the data (Overwriting the same location)
    end

    Readtask(32'h011);                  // Calling Read task
  endtask : Multiple_Writes_Single_Read_SameLocation_Test


// ------------------------- Perform Write followed by a Read to the same out-of-boundary address -------------------------
  task Outofboundary_Memory_Access_Test();
    Reset();                           	// Calling Reset task
    Writetask(32'h1111_1101, 32'hFFFFFFF0);  // Calling Write task
    Readtask(32'h1111_1101);                 // Calling Read task
  endtask : Outofboundary_Memory_Access_Test

// Random Write and Read sequence such that whenever a Read occurs, it will be to any of the addresses that were previously written
  task Random_Write_Read_Sequence();
  	int i = 0;									// internal variable to maintain a count of index
  	int x;										// internal variable to be randomized with in-line constraint
	bit [31:0] addr_queue [$];					// Declaring a queue to store the Write Addresses

	if (wr_en)
	begin
		addr_queue.push_front(Write_Address);	// storing the Write Addresses in the queue
		i++;									// keeping a track of the number of queue elements
	end
	else
		Read_Address = addr_queue[x] with {x inside {[0:i]};}	// Reading from any of the previously Written addresses, the address to Read is picked randomly
  endtask : Random_Write_Read_Sequence


// ------------------------------------------ CONSTRAINTS ------------------------------------------
// Constraint for generating Miscellaneous testcases
  constraint c_array_a1 {
  addr_rand[0] == 32'h0; addr_rand[1] == 32'h111; addr_rand[2] == 32'hxxxx_xxxx;
  }


// ------------------------------------------ EXECUTE TASK ------------------------------------------
// Calling all the testcases tasks in this task
// All the testcases can be executed by calling this task in the environment class
task execute();
Write_Read_IntermediateLocation_Test();
Write_Read_FirstLocation_Test();
Write_Read_LastLocation_Test();
Write_Read_Sametime_SameLocation_Test();
Write_Read_Sametime_DifferentLocation_Test();
Multiple_Writes_Multiple_Reads_ConsecutiveLocations_Test();
Multiple_Writes_Multiple_Reads_RandomLocations_Test();
Multiple_Writes_Single_Read_SameLocation_Test();
Outofboundary_Memory_Access_Test();
repeat (100) Random_Write_Read_Sequence();

// Miscellaneous tests
// Testcase 1
Writetask(addr_rand[0],Write_Data);
Writetask(addr_rand[1],Write_Data);
Readtask(addr_rand[1]);
Readtask(addr_rand[0]);

// Testcase 2
Readtask(addr_rand[1]);
Readtask(addr_rand[0]);
Writetask(addr_rand[0],Write_Data);
Writetask(addr_rand[1],Write_Data);

// Testcase 3
// Injecting error by writing at an unknown location and then Reading from it
Writetask(addr_rand[2],Write_Data);
Readtask(addr_rand[2]);

// Testcase 4
Writetask(addr_rand[5],Write_Data);
Writetask(addr_rand[7],Write_Data);
Readtask(addr_rand[5]);
Writetask(addr_rand[10],Write_Data);
Readtask(addr_rand[7]);
Writetask(addr_rand[6],Write_Data);
Readtask(addr_rand[10]);
endtask : execute


/* Working on this logic hence commenting as of now
  // Constraining in a way that only one of read or write can happen at once
  // Implementing constrained randomization to perform write followed by read to same random location
  constraint c_enable_signal {
    if(temp_en == 1) begin
      rd_en == 1;
      wr_en == 0;
    end
    else begin
      rd_en == 0;
      wr_en == 1;
    end
                            }
  // Pre-randomize function
  function void pre_randomize();
  	begin: pre_rand
    if(temp_en==1) begin
      Read_Address.rand_mode(0);
      Write_Address.rand_mode(0);
    end
    else begin
      Read_Address.rand_mode(1);
      Write_Address.rand_mode(1);
    end
	end: pre_rand
  endfunction

  // Post-randomize function
  function void post_randomize();
  	begin: post_rand
    temp_en = wr_en;
	end : post_rand
  endfunction : post_randomize();


endclass : Randomization

*/

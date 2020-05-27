///////////////////////////////////////////////////////////////////////////////
// Top.sv - Top module for AXI4 Lite Bus
//
// Author: Preetha Selvaraju, Disha Shetty, Rutuja Patil, Likitha Atluru
// Date: 18-Mar-2020
//
// Description:
// ------------
// Contains a top module which drives the master to perform read and write operations.
// Has several test cases to verify the functionality of the AXI4 Lite bus.
////////////////////////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;

module Top;

// declare the parameters
parameter CLK_PERIOD = 10;                            // clock period is 10 time units

// declare the internal variables
logic ACLK;                                           // system clock
logic ARESETN;                                        // system reset, active low
logic rd_en, wr_en;                                   // read and write enable
logic [Addr_Width-1:0] Read_Address, Write_Address;   // read and write address variables
logic [Data_Width-1:0] Write_Data;                    // write data variable
logic [31:0] i;                                       // loop variable

// instantiate the interface
axi4_lite_if A(.*);

// instantiate the master module
axi4_lite_master MP(
		.rd_en(rd_en),
		.wr_en(wr_en),
		.Read_Address(Read_Address),
		.Write_Address(Write_Address),
		.Write_Data(Write_Data),
		.M(A.master_if)
);


// instantiate the slave module
axi4_lite_slave SP(

        .S(A.slave_if)

        );


// clock generator
initial begin
	ACLK = 0;
	forever #(CLK_PERIOD / 2) ACLK = ~ACLK;
end

 
// define tasks for various testcases

// reading the default values in the first 20 locations of the memory
task default_read;
$display("\n\nReading the default values in the first 20 locations of the memory\n");
@(posedge ACLK) ARESETN = 1; rd_en = 1;
for(i=0; i<20; i++)
begin
	Read_Address = i;
	repeat(5)  @(posedge ACLK);
	$display($time, "\tInput Read Address: %h | Read Address(ARADDR): %h | Default Read Data(RDATA): %h | Default data in memory array(mem): %h", Read_Address, A.ARADDR, A.RDATA, SP.mem[i]);
end
endtask


// write to a single location 
task single_write;
$display("\n\nWrite to a single location");
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'h111; Write_Data=32'hfa88f4;
repeat(5) @(posedge ACLK);
$display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, SP.mem[Write_Address]);
endtask


// read from a single location 
task single_read;
$display("\n\nRead from a single location");
ARESETN = 1;
@(posedge ACLK)	ARESETN = 1; rd_en = 1; Read_Address=32'h111; 
repeat(5) @(posedge ACLK);
$display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, A.ARADDR, A.RDATA, SP.mem[Read_Address]);
endtask


// write and read at the same time to different locations
task write_read_diff_location_same_time;
$display("\n\nWrite and read at the same time to different locations");
repeat(5) @(posedge ACLK);
@(posedge ACLK) wr_en = 1; rd_en = 1;  Write_Address = 32'h678; Write_Data = 32'h01; Read_Address = 32'h111;
@(posedge ACLK) wr_en = 0; rd_en = 0;
repeat(5) @(posedge ACLK);
$display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, SP.mem[Write_Address]);
$display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, A.ARADDR, A.RDATA, SP.mem[Read_Address]);
endtask


// write and read at the same time to same location and check if read and write data matches
task  write_read_same_location_same_time;
$display("\n\nwrite and read at the same time to same location and check if read and write data match");
repeat(5) @(posedge ACLK);
@(posedge ACLK) ARESETN = 0;
@(posedge ACLK) ARESETN = 1; wr_en = 1; rd_en = 1;  Write_Address = 32'h1111; Write_Data = 32'h01; Read_Address = 32'b1111;
@(posedge ACLK) wr_en = 0; rd_en = 0;
repeat(5) @(posedge ACLK);
//$display("Input Write Address: %h | Input Write Data: %h | Input Read Address: %h | Write Address(AWADDR): %h | Read Address(ARADDR): %h | Write data(WDATA): %h, Read data(RDATA): %h", Write_Address, Write_Data, Read_Address, A.AWADDR, A.ARADDR, A.WDATA, A.RDATA);
if(A.RDATA == A.WDATA)
$display("Address: %h | Write Data: %h | Read Data: %h | Data Match", Write_Address, A.WDATA, A.RDATA);
else
$display("Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Write_Address, A.WDATA, A.RDATA);
endtask


// multiple write followed by multiple reads to consecutive locations and check if the write and read data matches
task multiple_writes_reads_consecutive_locations;
$display("\n\nmultiple writes followed by multiple reads to consecutive locations and check if the write and read data match");
// multiple writes to consecutive locations
ARESETN = 0;
@(posedge ACLK); ARESETN = 1; wr_en = 1; rd_en = 0;
for(i=0; i<10; i=i+1)
begin
Write_Address = i + 1;
Write_Data = i + $urandom_range(65526);
repeat(5) @(posedge ACLK);
end
// multiple reads from the consecutive locations
@(posedge ACLK); rd_en = 1; wr_en = 0;
for(i=0; i<10; i=i+1)
begin
Read_Address = i + 1;
repeat(5) @(posedge ACLK);
if(SP.mem[Read_Address] == A.RDATA)
$display("Address: %h | Write Data: %h | Read Data: %h | Data Match", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display("Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Read_Address, SP.mem[Read_Address], A.RDATA);
end
endtask


// multiple writes followed by multiple reads to random locations and check if the write and read data matches
task multiple_writes_reads_random_locations;
logic [31:0] Rand_Address [10];
$display("\n\nmultiple writes followed by multiple reads to random locations and check if the write and read data match");
// multiple writes to random locations
ARESETN = 0;
@(posedge ACLK); ARESETN = 1; wr_en = 1; rd_en = 0;
for(i=0; i<10; i=i+1)
begin
Write_Address = i + $urandom_range(4086);
Rand_Address [i] = Write_Address; 
Write_Data = i + 1;
repeat(5) @(posedge ACLK);
end
// multiple reads from the same random locations
@(posedge ACLK); rd_en = 1; wr_en = 0;
for(i=0; i<10; i=i+1)
begin
Read_Address = Rand_Address [i];
repeat(5) @(posedge ACLK);
if(SP.mem[Read_Address] == A.RDATA)
$display("Read Address: %h | Write Data: %h | Read Data: %h | Data Match", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display("Read Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Read_Address, SP.mem[Read_Address], A.RDATA);
end
endtask

// multiple writes followed by a single read to the same location and check if the last data written and read data matches
task multiple_writes_single_read_same_location;
$display("\n\nmultiple writes followed by a single read to the same location and check if the last data written and read data match");
// consecutive writes to the same location
ARESETN = 0;
@(posedge ACLK); ARESETN = 1; wr_en = 1; rd_en = 0; Write_Address = 'haf; 
for(i=0; i<10; i=i+1)
begin
Write_Data = i + 4;
repeat(5) @(posedge ACLK);
end
// single read from the same location
@(posedge ACLK); rd_en = 1; wr_en = 0;
Read_Address = 'haf;
repeat(5) @(posedge ACLK);
if(SP.mem[Read_Address] == A.RDATA)
$display("Address: %h | Write Data: %h | Read Data: %h | Data Match", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display("Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Read_Address, SP.mem[Read_Address], A.RDATA);

endtask


// single write followed by multiple reads to the same location and check if the read data matches the write data all the time
task single_write_multiple_reads_same_location;
$display("\n\nmultiple writes followed by a single read to the same location and check if the read data matches the write data all the time");
// single write to a particular location
ARESETN = 0;
@(posedge ACLK); ARESETN = 1; wr_en = 1; rd_en = 0; Write_Address = 'h123; Write_Data = 'hddd; 
repeat(5) @(posedge ACLK);
// single read from the same location
@(posedge ACLK); rd_en = 1; wr_en = 0;
for(i=0; i<10; i=i+1)
begin
Read_Address = 'h123;
repeat(5) @(posedge ACLK);
if(SP.mem[Read_Address] == A.RDATA)
$display("Address: %h | Write Data: %h | Read Data: %h | Data Match", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display("Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Read_Address, SP.mem[Read_Address], A.RDATA);
end
endtask

// reset in middle of write
task reset_write;
@(posedge ACLK) ARESETN = 0;
$display("\n\nreset in middle of write");
@(posedge ACLK) ARESETN = 1; wr_en = 1; rd_en = 0;
Write_Address=32'b10; Write_Data=32'h6ccc; 
//$monitor("Write Address %h, Write Data %h, WDATA %h, mem %h, AWVALID %b, AWREADY %b, WVALID %b, WREADY %b, BVALID %b, BREADY %b", Write_Address, Write_Data, A.WDATA, SP.mem[Write_Address], A.AWVALID, A.AWREADY, A.WVALID, A.WREADY, A.BVALID, A.BREADY);

@(posedge ACLK) ARESETN = 0;
@(posedge ACLK); ARESETN = 1; rd_en = 1; wr_en = 0; Read_Address = 32'hb;
repeat(5) @(posedge ACLK);
$display("Write Address %h, Write Data %h, mem %h", Write_Address, Write_Data, SP.mem[Read_Address]);
endtask


// reset in middle of read
task reset_read;
$display("\n\nreset in middle of read");
@(posedge ACLK) ARESETN = 0;
@(posedge ACLK) ARESETN = 1; rd_en = 0; wr_en = 1; Write_Address = 32'hab; Write_Data = 32'hab;
repeat(5) @(posedge ACLK);
@(posedge ACLK) rd_en = 0; wr_en = 0;
Read_Address=32'hab; 
//$monitor("Read Address %h, mem %h, ARVALID %b, ARREADY %b, RVALID %b, RREADY %b", Read_Address, SP.mem[Read_Address], A.ARVALID, A.ARREADY, A.RVALID, A.RREADY);
@(posedge ACLK);
@(posedge ACLK) ARESETN = 1;
@(posedge ACLK);
$display("Read Address %h, mem %h, RDATA %h", Read_Address, SP.mem[Read_Address], A.RDATA);
endtask


// Check for out of limit input write address 
task write_address_out_of_limit;
$display("\n\nCheck for out of limit input write address");
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'haaaaaaa; Write_Data=32'h68f48f4;
repeat(5) @(posedge ACLK);
$display("Input Write Address: %h | Input Write Data: %h | Write Address(AWADDR): %h | Write data(WDATA): %h | Data in memory array(mem): %h", Write_Address, Write_Data, A.AWADDR, A.WDATA, SP.mem[Write_Address]);
endtask


// Check for out of limit input read address 
task read_address_out_of_limit;
$display("\n\nCheck for out of limit input read address");
ARESETN = 0;
@(posedge ACLK)	ARESETN = 1; rd_en = 1; Read_Address=32'haaaaaaa; 
repeat(5) @(posedge ACLK);
$display("Input Read Address: %h | Read Address(AWADDR): %h | Read data(RDATA): %h | Data in memory array(mem): %h", Read_Address, A.ARADDR, A.RDATA, SP.mem[Read_Address]);
endtask



// write and read to all locations and check if data matches
task write_read_all_locations;
$display("\n\nmultiple writes followed by multiple reads to all locations and check if the write and read data matches");
// multiple writes to all locations
ARESETN = 0;
@(posedge ACLK); ARESETN = 1; wr_en = 1; rd_en = 0;
for(i=0; i<4096; i=i+1)
begin
Write_Address = i ;
Write_Data = $urandom_range(65535);
repeat(5) @(posedge ACLK);
end
// multiple reads from all locations
@(posedge ACLK); rd_en = 1; wr_en = 0;
for(i=0; i<4096; i=i+1)
begin
Read_Address = i ;
repeat(5) @(posedge ACLK);
if(SP.mem[Read_Address] == A.RDATA)
$display("Address: %h | Write Data: %h | Read Data: %h | Data Match", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display("Address: %h | Write Data: %h | Read Data: %h | Data Mismatch", Read_Address, SP.mem[Read_Address], A.RDATA);
end
endtask


// reset and call the tasks
initial 
begin

ARESETN = 0;
@(posedge ACLK) ARESETN = 1;
@(posedge ACLK) default_read;
repeat(10) @(posedge ACLK); 
@(posedge ACLK) single_write;
repeat(10) @(posedge ACLK); 
@(posedge ACLK) single_read;
repeat(10) @(posedge ACLK); 
@(posedge ACLK) write_read_diff_location_same_time;
repeat(10) @(posedge ACLK); 
@(posedge ACLK) write_read_same_location_same_time;
repeat(10) @(posedge ACLK); 
@(posedge ACLK) multiple_writes_reads_consecutive_locations;
repeat(50) @(posedge ACLK); 
@(posedge ACLK) multiple_writes_reads_random_locations;
repeat(50) @(posedge ACLK); 
@(posedge ACLK) multiple_writes_single_read_same_location;
repeat(50) @(posedge ACLK); 
@(posedge ACLK) single_write_multiple_reads_same_location;
repeat(50) @(posedge ACLK);
@(posedge ACLK) reset_write;
repeat(10) @(posedge ACLK);
@(posedge ACLK) reset_read;
repeat(50) @(posedge ACLK);
@(posedge ACLK) write_address_out_of_limit;
repeat(10) @(posedge ACLK);
@(posedge ACLK) read_address_out_of_limit;
repeat(10) @(posedge ACLK);
@(posedge ACLK) write_read_all_locations;
repeat(100) @(posedge ACLK); 
$stop;
end

endmodule: Top
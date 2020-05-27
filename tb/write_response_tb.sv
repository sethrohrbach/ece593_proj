//////////////////////////////////////////////////////////////
// write_response_tb.sv - Write Response Channel Testbench
//
// Author: Disha Shetty (dshetty@pdx.edu)
// Last modified by: Preetha Selvaraju (preet3@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Implements a testbench for write response channel of AXI4 Lite bus.
// Assertions are run along with the testcase to verify the 
// functionality of the write response channel.
//////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;   

module write_response_tb;

// declare the parameters
parameter CLK_PERIOD = 10;                            // clock period is 10 time units

// declare the internal variables
logic ACLK;                                           // system clock
logic ARESETN;                                        // system reset, active low 
logic rd_en;                                          // read enable signal 
logic wr_en;                                          // write enable signal
logic [Addr_Width-1:0] Read_Address, Write_Address;   // read and write address
logic [Data_Width-1:0] Write_Data;                    // write data value

// instantiate the AXI4 Lite bus interface
axi4_lite_if A(.*);                                  

// instantiate the master module
axi4_lite_master MP(                                 
		.rd_en(rd_en),
		.wr_en(wr_en),
		.Read_Address(Read_Address),
		.Write_Address(Write_Address),
		.Write_Data(Write_Data),
		.M(A.master_if)                       // interface as a master
);

// instantiate the slave module
axi4_lite_slave SP(                                  

        .S(A.slave_if)                                // interface as a slave

        );

// generate the system clock
initial begin
	ACLK = 0;
	forever #(CLK_PERIOD / 2) ACLK = ~ACLK;
end // clock generator


// perform single write followed by read to the same location and check if write and read data matches
initial
begin

$display("WRITE RESPONSE CHANNEL\n");
$display("Write followed by read to the same location\n");

// reset and start the system 
ARESETN = 0;

// monitor the values of address, data and signals of the channel
$monitor($time, " Time | ARESETN %d\n\t\t\t      Writing %h to   Address %h | AWVALID %d | AWREADY %d | WVALID %d | WREADY %d | BVALID %d | BREADY %d | Data in memory %h\n\t\t\t      Reading %h from Address %h | ARVALID %d | ARREADY %d | RVALID %d | RREADY %d\n", ARESETN, A.WDATA, A.AWADDR, A.AWVALID,A.AWREADY,A.WVALID,A.WREADY,A.BVALID,A.BREADY, SP.mem[Write_Address], A.RDATA, A.ARADDR, A.ARVALID,A.ARREADY,A.RVALID,A.RREADY);

// Write to a single location
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'ha9b; Write_Data=32'h1a2b3c4d;
repeat(5) @(posedge ACLK);

// Read from the same location
@(posedge ACLK) rd_en = 1; Read_Address=32'ha9b; 
repeat(5) @(posedge ACLK); ARESETN = 0; 
repeat(2) @(posedge ACLK);

// check if write and read data match
if(A.RDATA == SP.mem[Read_Address])
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MISMATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
$stop;
end



///////////////////////////////////////////////Write Response Channel Assertions//////////////////////////////////////////////////////////////////////////

// BVALID_RESET : When ARESETN goes low BVALID should go low
property BVALID_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.BVALID; 
endproperty: BVALID_RESET_p

BVALID_RESET_a: assert property(BVALID_RESET_p)
	$info("BVALID_RESET: ASSERTION PASS => When ARESETN goes low BVALID becomes low");
	else $error("BVALID_RESET: ASSERTION FAIL => When ARESETN goes low BVALID does not become low");


// BREADY_RESET : When ARESETN goes low BREADY should go low
property BREADY_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.BREADY; 
endproperty: BREADY_RESET_p

BREADY_RESET_a: assert property(BREADY_RESET_p)
	$info("BREADY_RESET: ASSERTION PASS => When ARESETN goes low BREADY becomes low");
	else $error("BREADY_RESET: ASSERTION FAIL => When ARESETN goes low BREADY does not become low");


// BVALID_X : A value of X on BVALID is not permitted when ARESETN is high
property BVALID_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.BVALID)); 
endproperty: BVALID_X_p

BVALID_X_a: assert property(BVALID_X_p)
	$info("BVALID_X: ASSERTION PASS => BVALID does not have X when ARESETN is high");
	else $info("BVALID_X: ASSERTION FAIL => BVALID has X when ARESETN is high");


// BREADY_X : A value of X on BREADY is not permitted when ARESETN is high
property BREADY_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.BREADY)); 
endproperty: BREADY_X_p

BREADY_X_a: assert property(BREADY_X_p)
	$info("BREADY_X: ASSERTION PASS => BREADY does not have X when ARESETN is high");
	else $info("BREADY_X: ASSERTION FAIL => BREADY has X when ARESETN is high");


// BVALID_STABLE : When BVALID is asserted, then it must remain asserted until BREADY is high
property BVALID_STABLE_p;
	@(posedge A.ACLK) $rose(A.BVALID) |-> (A.BVALID until_with A.BREADY);
endproperty: BVALID_STABLE_p

BVALID_STABLE_a: assert property(BVALID_STABLE_p)
	$info("BVALID_STABLE: ASSERTION PASS => When BVALID is asserted, then it remains asserted until BREADY is high");
	else $info("BVALID_STABLE: ASSERTION FAIL => When BVALID is asserted, then it does not remain asserted until BREADY is high");


// BVALID_STABLE - When BREADY is asserted, then it must remain asserted until BVALID is high
property BREADY_STABLE_p;
	@(posedge A.ACLK) $rose(A.BREADY) |-> (A.BREADY until_with A.BVALID);
endproperty: BREADY_STABLE_p

BREADY_STABLE_a: assert property(BREADY_STABLE_p)
	$info("BREADY_STABLE: ASSERTION PASS => When BREADY is asserted, then it remains asserted until BVALID is high");
	else $info("BREADY_STABLE: ASSERTION FAIL => When BREADY is asserted, then it does not remain asserted until BVALID is high");


endmodule: write_response_tb
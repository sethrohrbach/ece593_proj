//////////////////////////////////////////////////////////////
// read_data_tb.sv - Read Data Channel Testbench
//
// Author: Preetha Selvaraju (preet3@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Implements a testbench for read data channel of AXI4 Lite bus.
// Assertions are run along with the testcase to verify the 
// functionality of the read data channel.
//////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;   

module read_data_tb;

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

$display("READ DATA CHANNEL\n");
$display("Write followed by read to the same location\n");

// reset and start the system 
ARESETN = 0;

// monitor the values of address, data and signals of the channel
$monitor($time, " Time | ARESETN %d\n\t\t\t      Writing %h to   Address %h | AWVALID %d | AWREADY %d | WVALID %d | WREADY %d | BVALID %d | BREADY %d | Data in memory %h\n\t\t\t      Reading %h from Address %h | ARVALID %d | ARREADY %d | RVALID %d | RREADY %d\n", ARESETN, A.WDATA, A.AWADDR, A.AWVALID,A.AWREADY,A.WVALID,A.WREADY,A.BVALID,A.BREADY, SP.mem[Write_Address], A.RDATA, A.ARADDR, A.ARVALID,A.ARREADY,A.RVALID,A.RREADY);

// Write to a single location
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'hdef; Write_Data=32'h87654321;
repeat(5) @(posedge ACLK);

// Read from the same location
@(posedge ACLK) rd_en = 1; Read_Address=32'hdef; 
repeat(5) @(posedge ACLK); ARESETN = 0; 
repeat(2) @(posedge ACLK);

// check if write and read data match
if(A.RDATA == SP.mem[Read_Address])
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MISMATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
$stop;
end


///////////////////////////////////////////////////////////Read Data Channel Assertions//////////////////////////////////////////////////////////////////////////////////////////////

// READDATA : Check whether Read Data has been read successfully by the master
property READ_DATA_p;
	@(posedge A.ACLK) (A.RVALID & A.RREADY) |-> (A.RDATA == SP.mem[Read_Address]);
endproperty: READ_DATA_p

READ_DATA_a: assert property(READ_DATA_p)
	$info("READ_DATA: ASSERTION PASS => Read Data has been read successfully by the master\n\n");
	else $info("READ_DATA: ASSERTION FAIL => Read Data has not been read successfully by the master\n\n");


// RDATA_X : A value of X on RDATA valid byte lanes is not permitted when RVALID is high 
property RDATA_X_p;
	@(posedge A.ACLK) A.RVALID |-> not $isunknown(A.RDATA);
endproperty: RDATA_X_p

RDATA_X_a: assert property(RDATA_X_p)
	$info("RDATA_X: ASSERTION PASS => RDATA does not have X when RVALID is high\n\n");
	else $error("RDATA_X: ASSERTION FAIL => RDATA does not have X when RVALID is high\n\n");


// RVALID_RESET : When ARESETN goes low RVALID should go low
property RVALID_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.RVALID; 
endproperty: RVALID_RESET_p

RVALID_RESET_a: assert property(RVALID_RESET_p)
	$info("RVALID_RESET: ASSERTION PASS => When ARESETN goes low RVALID becomes low");
	else $error("RVALID_RESET: ASSERTION FAIL => When ARESETN goes low RVALID does not become low");


// RREADY_RESET : When ARESETN goes low RREADY should go low
property RREADY_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.RREADY; 
endproperty: RREADY_RESET_p

RREADY_RESET_a: assert property(RREADY_RESET_p)
	$info("RREADY_RESET: ASSERTION PASS => When ARESETN goes low RREADY becomes low");
	else $error("RREADY_RESET: ASSERTION FAIL => When ARESETN goes low RREADY does not become low");


// RVALID_STABLE : When RVALID is asserted, then it must remain asserted until RREADY is high
property RVALID_STABLE_p;
	@(posedge A.ACLK) $rose(A.RVALID) |-> (A.RVALID until_with A.RREADY);
endproperty: RVALID_STABLE_p

RVALID_STABLE_a: assert property(RVALID_STABLE_p)
	$info("RVALID_STABLE: ASSERTION PASS => When RVALID is asserted, then it remains asserted until RREADY is high");
	else $info("RVALID_STABLE: ASSERTION FAIL => When RVALID is asserted, then it does not remain asserted until RREADY is high");


// RREADY_STABLE : When RREADY is asserted, then it must remain asserted until RVALID is high
property RREADY_STABLE_p;
	@(posedge A.ACLK) $rose(A.RREADY) |-> (A.RREADY until_with A.RVALID);
endproperty: RREADY_STABLE_p

RREADY_STABLE_a: assert property(RREADY_STABLE_p)
	$info("RREADY_STABLE: ASSERTION PASS => When RREADY is asserted, then it remains asserted until RVALID is high");
	else $info("RREADY_STABLE: ASSERTION FAIL => When RREADY is asserted, then it does not remain asserted until RVALID is high");


// RVALID_X : A value of X on RVALID is not permitted when ARESETN is high
property RVALID_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.RVALID)); 
endproperty: RVALID_X_p

RVALID_X_a: assert property(RVALID_X_p)
	$info("RVALID_X: ASSERTION PASS => RVALID does not have X when ARESETN is high");
	else $info("RVALID_X: ASSERTION FAIL => RVALID has X when ARESETN is high");


// RREADY_X : A value of X on RREADY is not permitted when ARESETN is high
property RREADY_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.RREADY)); 
endproperty: RREADY_X_p

RREADY_X_a: assert property(RREADY_X_p)
	$info("RREADY_X: ASSERTION PASS => RREADY does not have X when ARESETN is high");
	else $info("RREADY_X: ASSERTION FAIL => RREADY has X when ARESETN is high");

//RDATA_STABLE : When RVALID is asserted, RDATA must remain stable until RVALID and RREADY become low
property RDATA_STABLE_p;
@(posedge A.ACLK) $rose(A.RVALID) |=> $stable(A.RDATA) until ((A.RREADY==0) && (A.RVALID==0)); 
endproperty: RDATA_STABLE_p

RDATA_STABLE_a: assert property(RDATA_STABLE_p) 
	$info("RDATA_STABLE: ASSERTION PASS => When RVALID is asserted, RDATA remains stable until RVALID and RREADY become low");
	else $error ("RDATA_STABLE: ASSERTION FAIL => When RVALID is asserted, RDATA does not remain stable until RVALID and RREADY become low") ;

endmodule: read_data_tb
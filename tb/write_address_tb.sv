//////////////////////////////////////////////////////////////
// write_address_tb.sv - Write Address Channel Testbench
//
// Author: Disha Shetty (dshetty@pdx.edu)
// Last modified by: Preetha Selvaraju (preet3@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Implements a testbench for write address channel of AXI4 Lite bus.
// Assertions are run along with the testcase to verify the 
// functionality of the write address channel.
//////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;   

module write_address_tb;

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
$display("WRITE ADDRESS CHANNEL\n");
$display("Write followed by read to the same location\n");

// reset and start the system 
ARESETN = 0;

// monitor the values of address, data and signals of the channel
$monitor($time, " Time | ARESETN %d\n\t\t\t      Writing %h to   Address %h | AWVALID %d | AWREADY %d | WVALID %d | WREADY %d | BVALID %d | BREADY %d | Data in memory %h\n\t\t\t      Reading %h from Address %h | ARVALID %d | ARREADY %d | RVALID %d | RREADY %d\n", ARESETN, A.WDATA, A.AWADDR, A.AWVALID,A.AWREADY,A.WVALID,A.WREADY,A.BVALID,A.BREADY, SP.mem[Write_Address], A.RDATA, A.ARADDR, A.ARVALID,A.ARREADY,A.RVALID,A.RREADY);

// Write to a single location
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'h246; Write_Data=32'h24681357;
repeat(5) @(posedge ACLK);

// Read from the same location
@(posedge ACLK) rd_en = 1; Read_Address=32'h246; 
repeat(5) @(posedge ACLK); ARESETN = 0; 
repeat(2) @(posedge ACLK);

// check if write and read data match
if(A.RDATA == SP.mem[Read_Address])
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MISMATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
$stop;
end


//////////////////////////////////////////////////////////Write Address Channel Assertions////////////////////////////////////////////////////////////////////////

//AWADDR_STABLE : When AWVALID is asserted, AWADDR must remain stable until AWVALID and AWREADY become low 
property AWADDR_STABLE_p ;
@(posedge A.ACLK) $rose(A.AWVALID) |=> $stable(A.AWADDR) until ((A.AWREADY==0) && (A.AWVALID==0)); 
endproperty:AWADDR_STABLE_p

AWADDR_STABLE_a: assert property(AWADDR_STABLE_p) 
	$info("AWADDR_STABLE: ASSERTION PASS => When AWVALID is asserted, AWADDR remains stable until AWVALID and AWREADY become low ");
	else $error ("AWADDR_STABLE: ASSERTION FAIL => When AWVALID is asserted, AWADDR does not remain stable until AWVALID and AWREADY become low") ;


// AWADDR_X : A value of X on AWADDR is not permitted when AWVALID is high
property AWADDR_X_p;
@(posedge A.ACLK) A.AWVALID |-> not ($isunknown(A.AWADDR)); 
endproperty: AWADDR_X_p

AWADDR_X_a: assert property(AWADDR_X_p)
	$info("AWADDR_X: ASSERTION PASS => AWADDR does not have X when AWVALID is high");
	 else $error("AWADDR_X: ASSERTION FAIL => AWADDR has X when AWVALID is high");


// AWVALID_RESET : When ARESETN goes low AWVALID should go low
property AWVALID_RESET_p;
@(posedge A.ACLK) (A.ARESETN==0) |-> not A.AWVALID ;
endproperty: AWVALID_RESET_p 

AWVALID_RESET_a: assert property(AWVALID_RESET_p) 
	$info("AWVALID_RESET: ASSERTION PASS => When ARESETN goes low AWVALID becomes low");
	else $error ("AWVALID_RESET: ASSERTION FAIL => When ARESETN goes low AWVALID does not become low") ;


// AWREADY_RESET : When ARESETN goes low AWREADY should go low
property AWREADY_RESET_p;
@(posedge A.ACLK) (A.ARESETN==0) |-> not A.AWREADY ;
endproperty: AWREADY_RESET_p 

AWREADY_RESET_a: assert property(AWREADY_RESET_p) 
	$info("AWREADY_RESET: ASSERTION PASS => When ARESETN goes low AWREADY becomes low");
	else $error ("AWREADY_RESET: ASSERTION FAIL => When ARESETN goes low AWREADY does not become low") ;


// AWVALID_STABLE : When AWVALID is asserted, then it must remain asserted until AWREADY is high
property AWVALID_STABLE_p;
@(posedge A.ACLK) $rose(A.AWVALID) |-> A.AWVALID until_with A.AWREADY;
endproperty: AWVALID_STABLE_p

AWVALID_STABLE_a: assert property(AWVALID_STABLE_p) 
	$info("AWVALID_STABLE: ASSERTION PASS => When AWVALID is asserted, then it remains asserted until AWREADY is high");
	else $error("AWVALID_STABLE: ASSERTION FAIL => When AWVALID is asserted, then it does not remain asserted until AWREADY is high");


// AWREADY_STABLE : When AWREADY is asserted, then it must remain asserted until AWVALID is high
property AWREADY_STABLE_p;
@(posedge A.ACLK) $rose(A.AWREADY) |-> A.AWREADY until_with A.AWVALID;
endproperty: AWREADY_STABLE_p

AWREADY_STABLE_a: assert property(AWREADY_STABLE_p) 
	$info("AWREADY_STABLE: ASSERTION PASS => When AWREADY is asserted, then it remains asserted until AWVALID is high");
	else $error("AWREADY_STABLE: ASSERTION FAIL => When AWREADY is asserted, then it does not remain asserted until AWVALID is high");


// AWVALID_X : A value of X on AWVALID is not permitted when ARESETN is high
property AWVALID_X_p;
@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.AWVALID));
endproperty: AWVALID_X_p

AWVALID_X_a: assert property(AWVALID_X_p) 
	$info("AWVALID_X: ASSERTION PASS => AWVALID does not have X when ARESETN is high");
	else $error ("AWVALID_X: ASSERTION FAIL => AWVALID has X when ARESETN is high");


//AWREADY_X - A value of X on AWREADY is not permitted when ARESETN is high
property AWREADY_X_p;
@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.AWREADY));
endproperty:AWREADY_X_p

AWREADY_X_a: assert property(AWREADY_X_p) 
	$info("AWREADY_X: ASSERTION PASS => AWVALID does not have X when ARESETN is high");
	else $error ("AWREADY_X: ASSERTION FAIL => AWVALID has X when ARESETN is high");


// WRITEADDRESS - Check whether Write Address has been received successfully by the slave
property WRITE_ADDRESS_p;
	@(posedge A.ACLK) (A.AWVALID & A.AWREADY) |-> (A.AWADDR == Write_Address);
endproperty: WRITE_ADDRESS_p

WRITE_ADDRESS_a: assert property(WRITE_ADDRESS_p)
	$info("WRITE_ADDRESS: ASSERTION PASS => Write Address has been received successfully by the slave");
	else $info("WRITE_ADDRESS: ASSERTION FAIL => Write Address has been received successfully by the slave");


endmodule: write_address_tb


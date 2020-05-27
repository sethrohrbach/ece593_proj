//////////////////////////////////////////////////////////////
// read_address_tb.sv - Read Address Channel Testbench
//
// Author: Likitha Atluru (latluru@pdx.edu)
// Last modified by: Preetha Selvaraju (preet3@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Implements a testbench for read address channel of AXI4 Lite bus.
// Assertions are run along with the testcase to verify the 
// functionality of the read address channel.
//////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;   

module read_address_tb;

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


// perform single write followed by read to the same location and check if write and read data match
initial
begin

$display("READ ADDRESS CHANNEL\n");
$display("Write followed by read to the same location\n");

// reset and start the system 
ARESETN = 0;

// monitor the values of address, data and signals of the channel
$monitor($time, " Time | ARESETN %d\n\t\t\t      Writing %h to   Address %h | AWVALID %d | AWREADY %d | WVALID %d | WREADY %d | BVALID %d | BREADY %d | Data in memory %h\n\t\t\t      Reading %h from Address %h | ARVALID %d | ARREADY %d | RVALID %d | RREADY %d\n", ARESETN, A.WDATA, A.AWADDR, A.AWVALID,A.AWREADY,A.WVALID,A.WREADY,A.BVALID,A.BREADY, SP.mem[Write_Address], A.RDATA, A.ARADDR, A.ARVALID,A.ARREADY,A.RVALID,A.RREADY);

// Write to a single location
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'habc; Write_Data=32'h12345678;
repeat(5) @(posedge ACLK);

// Read from the same location
@(posedge ACLK) rd_en = 1; Read_Address=32'habc; 
repeat(5) @(posedge ACLK); ARESETN = 0; 
repeat(2) @(posedge ACLK);

// check if write and read data match
if(A.RDATA == SP.mem[Read_Address])
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MISMATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
$stop;
end



///////////////////////////////////////////////////////////Assertions for Read Address Channel//////////////////////////////////////////////////////////////////////

//ARADDR_STABLE : when ARVALID is asserted, address ARADDR remains stable until ARVALID and ARREADY become low 
property ARADDR_STABLE_p ;
@(posedge A.ACLK) $rose(A.ARVALID) |=> $stable(A.ARADDR) until ((A.ARREADY==0) && (A.ARVALID==0)); 
endproperty:ARADDR_STABLE_p

ARADDR_STABLE_a: assert property(ARADDR_STABLE_p) 
	$info("ARADDR_STABLE: ASSERTION PASS | When ARVALID is asserted, ARADDR remains stable until ARVALID and ARREADY become low\n\n");
	else $error ("ARADDR_STABLE: ASSERTION FAIL | When ARVALID is asserted, ARADDR does not remain stable until ARVALID and ARREADY become low\n\n") ;


// ARADDR_X : A value of X on ARADDR is not permitted when ARVALID is high
property ARADDR_X_p;
@(posedge A.ACLK) A.ARVALID |-> not ($isunknown(A.ARADDR)); 
endproperty: ARADDR_X_p

ARADDR_X_a: assert property(ARADDR_X_p)
	$info("ARADDR_X: ASSERTION PASS => ARADDR does not have X when ARVALID is high\n");
	 else $error("ARADDR_X: ASSERTION FAIL => ARADDR has X when ARVALID is high\n");


// ARVALID_RESET : When ARESETN goes low ARVALID should go low
property ARVALID_RESET_p;
@(posedge A.ACLK)  (A.ARESETN==0) |-> not A.ARVALID ;
endproperty: ARVALID_RESET_p 

ARVALID_RESET_a: assert property(ARVALID_RESET_p) 
	$info("ARVALID_RESET: ASSERTION PASS => When ARESETN goes low ARVALID becomes low\n");
	else $error ("ARVALID_RESET: ASSERTION FAIL => When ARESETN goes low ARVALID does not become low\n") ;


// ARREADY_RESET : When ARESETN goes low ARREADY should go low
property ARREADY_RESET_p;
@(posedge A.ACLK) (A.ARESETN==0) |-> not A.ARREADY ;
endproperty: ARREADY_RESET_p 

ARREADY_RESET_a: assert property(ARREADY_RESET_p) 
	$info("ARREADY_RESET: ASSERTION PASS => When ARESETN goes low ARREADY becomes low\n");
	else $error ("ARREADY_RESET: ASSERTION FAIL => When ARESETN goes low ARREADY does not become low\n") ;


// ARVALID_STABLE : When ARVALID is asserted, then it must remain asserted until ARREADY is high
property ARVALID_STABLE_p;
@(posedge A.ACLK) $rose(A.ARVALID) |-> A.ARVALID until_with A.ARREADY;
endproperty: ARVALID_STABLE_p

ARVALID_STABLE_a: assert property(ARVALID_STABLE_p) 
	$info("ARVALID_STABLE: ASSERTION PASS => When ARVALID is asserted, then it remains asserted until ARREADY is high\n");
	else $error("ARVALID_STABLE: ASSERTION FAIL => When ARVALID is asserted, then it does not remain asserted until ARREADY is high\n");


// ARVALID_STABLE : When ARREADY is asserted, then it must remain asserted until ARVALID is high 
property ARREADY_STABLE_p;
@(posedge A.ACLK) $rose(A.ARREADY) |-> A.ARREADY until_with A.ARVALID;
endproperty: ARREADY_STABLE_p

ARREADY_STABLE_a: assert property(ARREADY_STABLE_p) 
	$info("ARREADY_STABLE: ASSERTION PASS => When ARREADY is asserted, then it remains asserted until ARVALID is high\n");
	else $error("ARREADY_STABLE: ASSERTION FAIL => When ARREADY is asserted, then it does not remain asserted until ARVALID is high\n");


//ARVALID_X : A value of X on ARVALID is not permitted when ARESETN is high
property ARVALID_X_p;
@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.ARVALID));
endproperty: ARVALID_X_p

ARVALID_X_a: assert property(ARVALID_X_p) 
	$info("ARVALID_X: ASSERTION PASS => ARVALID does not have X when ARESETN is high\n");
	else $error ("ARVALID_X: ASSERTION FAIL => ARVALID has X when ARESETN is high\n");

//ARREADY_X : A value of X on ARREADY is not permitted when ARESETN is high 
property ARREADY_X_p;
@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.ARREADY));
endproperty: ARREADY_X_p

ARREADY_X_a: assert property(ARREADY_X_p) 
	$info("ARREADY_X: ASSERTION PASS => ARREADY does not have X when ARESETN is high\n");
	else $error ("ARREADY_X: ASSERTION FAIL => ARREADY has X when ARESETN is high\n");


// READADDRESS : Check whether ARADDR has been received successfully by the slave
property READ_ADDRESS_p;
	@(posedge A.ACLK) (A.ARVALID & A.ARREADY) |-> (A.ARADDR == Read_Address);
endproperty: READ_ADDRESS_p

READ_ADDRESS_a: assert property(READ_ADDRESS_p)
	$info("READ_ADDRESS: ASSERTION PASS => Read Address has been received successfully by the slave\n");
	else $error("READ_ADDRESS: ASSERTION FAIL => Read Address has not been received successfully by the slave\n");


endmodule: read_address_tb





















//////////////////////////////////////////////////////////////
// write_data_tb.sv - Write Data Channel Testbench
//
// Author: Rutuja Patil (rutuja@pdx.edu)
// Last modified by: Preetha Selvaraju (preet3@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Implements a testbench for write data channel of AXI4 Lite bus.
// Assertions are run along with the testcase to verify the 
// functionality of the write data channel.
//////////////////////////////////////////////////////////////

// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;   

module write_data_tb;

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

$display("WRITE DATA CHANNEL\n");
$display("Write followed by read to the same location\n");

// reset and start the system 
ARESETN = 0;

// monitor the values of address, data and signals of the channel
$monitor($time, " Time | ARESETN %d\n\t\t\t      Writing %h to   Address %h | AWVALID %d | AWREADY %d | WVALID %d | WREADY %d | BVALID %d | BREADY %d | Data in memory %h\n\t\t\t      Reading %h from Address %h | ARVALID %d | ARREADY %d | RVALID %d | RREADY %d\n", ARESETN, A.WDATA, A.AWADDR, A.AWVALID,A.AWREADY,A.WVALID,A.WREADY,A.BVALID,A.BREADY, SP.mem[Write_Address], A.RDATA, A.ARADDR, A.ARVALID,A.ARREADY,A.RVALID,A.RREADY);

// Write to a single location
@(posedge ACLK)	ARESETN = 1; wr_en = 1; Write_Address=32'h579; Write_Data=32'habcdef;
repeat(5) @(posedge ACLK);

// Read from the same location
@(posedge ACLK) rd_en = 1; Read_Address=32'h579; 
repeat(5) @(posedge ACLK); ARESETN = 0; 
repeat(2) @(posedge ACLK);

// check if write and read data match
if(A.RDATA == SP.mem[Read_Address])
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
else
$display($time, " Time\n\t\t\t      FINAL RESULT => ADDRESS: %h | WRITE DATA: %h | READ DATA: %h | DATA MISMATCH\n", Read_Address, SP.mem[Read_Address], A.RDATA);
$stop;
end


///////////////////////////////////////////////////////////Write Data Channel Assertions////////////////////////////////////////////////////////////////////////

// WDATA_STABLE : When WVALID is asserted, WDATA must remain stable until WVALID and WREADY become low 
property WDATA_STABLE_p;
@(posedge A.ACLK) $rose(A.WVALID) |=> $stable(A.WDATA) until ((A.WREADY==0) && (A.WVALID==0)); 
endproperty: WDATA_STABLE_p

WDATA_STABLE_a: assert property(WDATA_STABLE_p) 
	$info("WDATA_STABLE: ASSERTION PASS => When WVALID is asserted, WDATA remains stable until WVALID and WREADY become low");
	else $error ("WDATA_STABLE: ASSERTION FAIL => When WVALID is asserted, WDATA does not remain stable until WVALID and WREADY become low") ;


// WDATA : Check whether Write Data has been received successfully by the slave
property WRITE_DATA_p;
	@(posedge A.ACLK) (A.WVALID & A.WREADY) |-> (A.WDATA == SP.mem[Write_Address]);
endproperty: WRITE_DATA_p

WRITE_DATA_a: assert property(WRITE_DATA_p)
	$info("WRITE_DATA: ASSERTION PASS => Write Data has been received successfully by the slave");
	else $info("WRITE_DATA: ASSERTION FAIL => Write Data has not been received successfully by the slave");


// WDATA_X : A value of X on WDATA valid byte lanes is not permitted when WVALID is high
property WDATA_X_p;
	@(posedge A.ACLK) A.WVALID |-> not $isunknown(A.WDATA);
endproperty: WDATA_X_p

WDATA_X_p_a: assert property(WDATA_X_p)
	$info("WDATA_X: ASSERTION PASS => WDATA does not have X when WVALID is high");
	else $error("WDATA_X: ASSERTION FAIL => WDATA has X when WVALID is high");


// WVALID_RESET : When ARESETN goes low WVALID should go low
property WVALID_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.WVALID; 
endproperty: WVALID_RESET_p

WVALID_RESET_a: assert property(WVALID_RESET_p)
	$info("WVALID_RESET: ASSERTION PASS => When ARESETN goes low WVALID becomes low");
	else $error("WVALID_RESET: ASSERTION FAIL => When ARESETN goes low WVALID does not become low");


// WREADY_RESET : When ARESETN goes low WREADY should go low
property WREADY_RESET_p;
	@(posedge A.ACLK) (A.ARESETN==0) |-> not A.WREADY; 
endproperty: WREADY_RESET_p

WREADY_RESET_a: assert property(WREADY_RESET_p)
	$info("WREADY_RESET: ASSERTION PASS => When ARESETN goes low WREADY becomes low");
	else $error("WREADY_RESET: ASSERTION FAIL => When ARESETN goes low WREADY does not become low");



// WVALID_STABLE : When WVALID is asserted, then it must remain asserted until WREADY is high
property WVALID_STABLE_p;
	@(posedge A.ACLK) $rose(A.WVALID) |-> (A.WVALID until_with A.WREADY);
endproperty: WVALID_STABLE_p

WVALID_STABLE_a: assert property(WVALID_STABLE_p)
	$info("WVALID_STABLE: ASSERTION PASS => When WVALID is asserted, then it remains asserted until WREADY is high");
	else $info("WVALID_STABLE: ASSERTION FAIL => When WVALID is asserted, then it does not remain asserted until WREADY is high");



// WREADY_STABLE : When WREADY is asserted, then it must remain asserted until WVALID is high
property WREADY_STABLE_p;
	@(posedge A.ACLK) $rose(A.WREADY) |-> (A.WREADY until_with A.WVALID);
endproperty: WREADY_STABLE_p

WREADY_STABLE_a: assert property(WREADY_STABLE_p)
	$info("WREADY_STABLE: ASSERTION PASS => When RREADY is asserted, then it remains asserted until RVALID is high");
	else $info("WREADY_STABLE: ASSERTION FAIL => When RREADY is asserted, then it does not remain asserted until RVALID is high");


// WVALID_X : A value of X on WVALID is not permitted when ARESETN is high
property WVALID_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.WVALID)); 
endproperty: WVALID_X_p

WVALID_X_a: assert property(WVALID_X_p)
	$info("WVALID_X: ASSERTION PASS => WVALID deos not have X when ARESETN is high");
	else $info("WVALID_X: ASSERTION FAIL => WVALID is not permitted when ARESETN is high");


// WREADY_X : A value of X on WREADY is not permitted when ARESETN is high
property WREADY_X_p;
	@(posedge A.ACLK) (A.ARESETN==1) |-> not ($isunknown(A.WREADY)); 
endproperty: WREADY_X_p

WREADY_X_a: assert property(WREADY_X_p)
	$info("WREADY_X: ASSERTION PASS => WREADY does not have X when ARESETN is high");
	else $info("WREADY_X: ASSERTION FAIL => WREADY has X when ARESETN is high");


endmodule: write_data_tb






















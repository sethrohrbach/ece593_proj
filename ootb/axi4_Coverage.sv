////////////////////////////////////////////////////////////////
// axi4_coverage.sv - coverages.
//
// Author: Sumeet Pawar(pawar@pdx.edu), Surakshith Reddy Mothe(smothe@pdx.edu)
// Modified: May 14, 2020
//
// Description:
// ------------
// contains all covergroups for code coverage and functional coverage.
//
////////////////////////////////////////////////////////////////


// Including Master and Slave design files



// import the global definitions of AXI4 Lite bus
import axi4_lite_Defs::*;

// coverage class
class axi4_Coverage;

 logic rd_en;                                   // read enable signal
 logic wr_en;                                   // write enable signal
 logic [Addr_Width-1:0] Read_Address;           // input read address
 logic [Addr_Width-1:0] Write_Address;          // input write address
 logic [Data_Width-1:0] Write_Data;             // input write data

//Hook the coverage up with the AXI4:
  virtual axi4_lite_bfm bfm;


// ------------------------------------------------------- CODE COVERAGES -------------------------------------------------------
// Covergroup 1 for Read Address
covergroup cg_Read_Address @(posedge bfm.ACLK);
   Read_Address_Valid: coverpoint bfm.ARVALID iff (bfm.ARESETN) {   // Coverpoint for Read Address Valid signal
   	bins ARVALID_High = {1};
   	bins ARVALID_Low = {0};
   	}

	Read_Address_Ready: coverpoint bfm.ARREADY iff (bfm.ARESETN) {   // Coverpoint for Read Address Ready signal
   	bins ARREADY_High = {1};
   	bins ARREADY_Low = {0};
   	}

   	Read_Address: coverpoint bfm.ARADDR {                         // Coverpoint for Read Address
   	bins ARADDR_First_Location = {0};
   	wildcard bins ARADDR_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   	wildcard bins ARADDR_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}
endgroup : cg_Read_Address


// Covergroup 2 for Read Data
covergroup cg_Read_Data @(posedge bfm.ACLK);
   	Read_Data_Valid: coverpoint bfm.RVALID iff (bfm.ARESETN) {    // Coverpoint for Read Data Valid signal
		bins RVALID_High = {1};
   	bins RVALID_Low = {0};
   	}

	Read_Data_Ready: coverpoint bfm.RREADY iff (bfm.ARESETN) {       // Coverpoint for Read Data Ready signal
   		bins RREADY_High = {1};
   		bins RREADY_Low = {0};
   	}

   	Read_Data: coverpoint bfm.RDATA {                             // Coverpoint for Read Data
   	   bins RDATA_All_Zeros = {0};
   		bins RDATA_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   		bins RDATA_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_Read_Data


// Covergroup 3 for Write Address
covergroup cg_Write_Address @(posedge bfm.ACLK);
   	Write_Address_Valid: coverpoint bfm.AWVALID iff (bfm.ARESETN) {  // Coverpoint for Write Address Valid signal
	  	bins AWVALID_High = {1};
   	bins AWVALID_Low = {0};
   	}

	Write_Address_Ready: coverpoint bfm.AWREADY iff (bfm.ARESETN) {     // Coverpoint for Write Address Ready signal
   	  	bins AWREADY_High = {1};
   		bins AWREADY_Low = {0};
   	}

   	Write_Address: coverpoint bfm.AWADDR {                           // Coverpoint for Write Address signal
   		bins AWADDR_First_Location = {0};
   		wildcard bins AWADDR_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   		wildcard bins AWADDR_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}
endgroup : cg_Write_Address


// Covergroup 4 for Write Data
covergroup cg_Write_Data @(posedge bfm.ACLK);
   	Write_Data_Valid: coverpoint bfm.WVALID iff (bfm.ARESETN) {      // Coverpoint for Write Data Valid signal
   		bins WVALID_High = {1};
   		bins WVALID_Low = {0};
   	}

	Write_Data_Ready: coverpoint bfm.WREADY iff (bfm.ARESETN) {         // Coverpoint for Write Data Ready signal
   		bins WREADY_High = {1};
   		bins WREADY_Low = {0};
   	}

   	Write_Data: coverpoint bfm.WDATA {                               // Coverpoint for Write Data signal
   		bins WDATA_All_Zeros = {0};
   		bins WDATA_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   		bins WDATA_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_Write_Data


// Covergroup 5 for Write Response
covergroup cg_Write_Response @(posedge bfm.ACLK);
   	Write_Response_Valid: coverpoint bfm.BVALID iff (bfm.ARESETN) {  // Coverpoint for Write Response Valid signal
   		bins BVALID_High = {1};
   		bins BVALID_Low = {0};
   	}

	Write_Response_Ready: coverpoint bfm.BREADY iff (bfm.ARESETN) {     // Coverpoint for Write Response Ready signal
   		bins BREADY_High = {1};
   		bins BREADY_Low = {0};
   	}
endgroup : cg_Write_Response


// Covergroup 6 for CPU Signals
covergroup cg_CPU_Signals @(posedge bfm.ACLK);
   	CPU_Read_Enable: coverpoint rd_en {                              // Coverpoint for CPU Read Enable signal
   		bins rd_en_High = {1};
   		bins rd_en_Low = {0};
   	}

	CPU_Write_Enable: coverpoint wr_en {                                // Coverpoint for CPU Write Enable signal
   		bins wr_en_High = {1};
   		bins wr_en_Low = {0};
   	}

	CPU_Read_Address: coverpoint Read_Address {                         // Coverpoint for CPU Read Address
   		bins Read_Address_First_Location = {0};
   		wildcard bins Read_Address_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   		wildcard bins Read_Address_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}

	CPU_Write_Address: coverpoint Write_Address {                       // Coverpoint for CPU Write Address signal
   		bins Write_Address_First_Location = {0};
   		wildcard bins Write_Address_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   		wildcard bins Write_Address_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}

	CPU_Write_Data: coverpoint Write_Data {                             // Coverpoint for CPU Write Data signal
   		bins Write_Data_All_Zeros = {0};
   		bins Write_Data_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   		bins Write_Data_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_CPU_Signals


// ------------------------------------------------------- FUNCTIONAL COVERAGES -------------------------------------------------------
// Covergroup 7 for Master FSM
covergroup cg_Master_FSM @(posedge bfm.ACLK);
   	Master_Read_FSM: coverpoint axi4_lite_master.current_state_read iff (bfm.ARESETN) {   // Coverpoint for Master Read FSM
   		bins mr1 = (state.IDLE => state.ADDR);
   		bins mr2 = (state.ADDR => state.DATA);
   		bins mr3 = (state.DATA => state.RESP);
   		bins mr4 = (state.RESP => state.IDLE);
   		bins mr_sequence = (state.IDLE => state.ADDR => state.DATA => state.RESP => state.IDLE);
   		illegal_bins mr_illegal1 = (state.DATA => state.ADDR);
   		illegal_bins mr_illegal2 = (state.RESP => state.DATA);
   	  	illegal_bins mr_illegal3 = (state.RESP => state.ADDR);
   		illegal_bins mr_illegal4 = (state.IDLE => state.DATA);
   		illegal_bins mr_illegal5 = (state.IDLE => state.RESP);
   		illegal_bins mr_illegal6 = (state.ADDR => state.RESP);
   	}

   	Master_Write_FSM: coverpoint axi4_lite_master.current_state_write iff (bfm.ARESETN) {    // Coverpoint for Master Write FSM
   		bins mw1 = (state.IDLE => state.ADDR);
   		bins mw2 = (state.ADDR => state.DATA);
   		bins mw3 = (state.DATA => state.RESP);
   		bins mw4 = (state.RESP => state.IDLE);
   		bins mw_sequence = (state.IDLE => state.ADDR => state.DATA => state.RESP => state.IDLE);
   		illegal_bins mw_illegal1 = (state.DATA => state.ADDR);
   		illegal_bins mw_illegal2 = (state.RESP => state.DATA);
   	  	illegal_bins mw_illegal3 = (state.RESP => state.ADDR);
   		illegal_bins mw_illegal4 = (state.IDLE => state.DATA);
   		illegal_bins mw_illegal5 = (state.IDLE => state.RESP);
   		illegal_bins mw_illegal6 = (state.ADDR => state.RESP);
   	}
endgroup : cg_Master_FSM


// Covergroup 8 for Slave FSM
covergroup cg_Slave_FSM @(posedge bfm.ACLK);
   	Slave_Read_FSM: coverpoint axi4_lite_slave.current_state_read iff (bfm.ARESETN) {  // Coverpoint for Slave Read FSM
   		bins sr1 = (state.IDLE => state.ADDR);
   		bins sr2 = (state.ADDR => state.DATA);
   		bins sr3 = (state.DATA => state.RESP);
   		bins sr4 = (state.RESP => state.IDLE);
   		bins sr_sequence = (state.IDLE => state.ADDR => state.DATA => state.RESP => state.IDLE);
   		illegal_bins sr_illegal1 = (state.DATA => state.ADDR);
   		illegal_bins sr_illegal2 = (state.RESP => state.DATA);
   	  	illegal_bins sr_illegal3 = (state.RESP => state.ADDR);
   		illegal_bins sr_illegal4 = (state.IDLE => state.DATA);
   		illegal_bins sr_illegal5 = (state.IDLE => state.RESP);
   		illegal_bins sr_illegal6 = (state.ADDR => state.RESP);
   	}

   	Slave_Write_FSM: coverpoint axi4_lite_slave.current_state_write iff (bfm.ARESETN) {   // Coverpoint for Slave Write FSM
   	  	bins sw1 = (state.IDLE => state.ADDR);
   		bins sw2 = (state.ADDR => state.DATA);
   		bins sw3 = (state.DATA => state.RESP);
   		bins sw4 = (state.RESP => state.IDLE);
   		bins sw_sequence = (state.IDLE => state.ADDR => state.DATA => state.RESP => state.IDLE);
   		illegal_bins sw_illegal1 = (state.DATA => state.ADDR);
   		illegal_bins sw_illegal2 = (state.RESP => state.DATA);
   	  	illegal_bins sw_illegal3 = (state.RESP => state.ADDR);
   		illegal_bins sw_illegal4 = (state.IDLE => state.DATA);
   		illegal_bins sw_illegal5 = (state.IDLE => state.RESP);
   		illegal_bins sw_illegal6 = (state.ADDR => state.RESP);
   	}
endgroup : cg_Slave_FSM


// Covergroup 9 for Reset signals
covergroup cg_Reset_Signal @(posedge bfm.ACLK);

	Read_Address_Valid_Reset: coverpoint bfm.ARVALID iff (!(bfm.ARESETN)) {   // Coverpoint for Read Address Valid Signal
   		bins ARVALID_Low_Reset = {0};
   		illegal_bins ARVALID_High_Reset_illegal = {1};
   	}

	Read_Address_Ready_Reset: coverpoint bfm.ARREADY iff (!(bfm.ARESETN)) {   // Coverpoint for Read Address Ready Signal
   		bins ARREADY_Low_Reset = {0};
   	   	illegal_bins ARREADY_High_Reset_illegal = {1};
   	}

   Read_Data_Valid_Reset: coverpoint bfm.RVALID iff (!(bfm.ARESETN)) {       // Coverpoint for Read Data Valid Signal
   		bins RVALID_Low_Reset = {0};
   		illegal_bins RVALID_High_Reset_illegal = {1};
   	}

	Read_Data_Ready_Reset: coverpoint bfm.RREADY iff (!(bfm.ARESETN)) {       // Coverpoint for Read Data Ready Signal
   		bins RREADY_Low_Reset = {0};
   		illegal_bins RREADY_High_Reset_illegal = {1};
   	}

   Write_Address_Valid_Reset: coverpoint bfm.AWVALID iff (!(bfm.ARESETN)) {  // Coverpoint for Write Address Valid Signal
   		bins AWVALID_Low_Reset = {0};
	  	   illegal_bins AWVALID_High_Reset_illegal = {1};
   	}

	Write_Address_Ready_Reset: coverpoint bfm.AWREADY iff (!(bfm.ARESETN)) {  // Coverpoint for Write Address Ready Signal
   		bins AWREADY_Low_Reset = {0};
   	  	illegal_bins AWREADY_High_Reset_illegal = {1};
   	}

   Write_Data_Valid_Reset: coverpoint bfm.WVALID iff (!(bfm.ARESETN)) {      // Coverpoint for Write Data Valid Signal
   		bins WVALID_Low_Reset = {0};
   		illegal_bins WVALID_High_Reset_illegal = {1};
   	}

	Write_Data_Ready_Reset: coverpoint bfm.WREADY iff (!(bfm.ARESETN)) {      // Coverpoint for Write Data Ready Signal
   		bins WREADY_Low_Reset = {0};
   		illegal_bins WREADY_High_Reset_illegal = {1};
   	}

   Write_Response_Valid_Reset: coverpoint bfm.BVALID iff (!(bfm.ARESETN)) {   // Coverpoint for Write Response Valid Signal
   		bins BVALID_Low_Reset = {0};
   		illegal_bins BVALID_High_Reset_illegal = {1};
   	}

	Write_Response_Ready_Reset: coverpoint bfm.BREADY iff (!(bfm.ARESETN)) {  // Coverpoint for Write Response Ready Signal
   		bins BREADY_Low_Reset = {0};
   		illegal_bins BREADY_High_Reset_illegal = {1};
   	}

   	Master_Read_FSM_Reset: coverpoint axi4_lite_master.current_state_read iff (!(bfm.ARESETN)) {   // Coverpoint for Master Read FSM
   		bins mr_reset1 = (state.ADDR => state.IDLE);
   		bins mr_reset2 = (state.DATA => state.IDLE);
   		bins mr_reset3 = (state.RESP => state.IDLE);
   		illegal_bins mr_illegal1 = (state.IDLE => state.ADDR);
   		illegal_bins mr_illegal2 = (state.ADDR => state.DATA);
   		illegal_bins mr_illegal3 = (state.DATA => state.RESP);
   		illegal_bins mr_illegal4 = (state.DATA => state.ADDR);
   	   illegal_bins mr_illegal5 = (state.RESP => state.DATA);
   	  	illegal_bins mr_illegal6 = (state.RESP => state.ADDR);
   	   illegal_bins mr_illegal7 = (state.IDLE => state.DATA);
   	   illegal_bins mr_illegal8 = (state.IDLE => state.RESP);
   	   illegal_bins mr_illegal9 = (state.ADDR => state.RESP);

   	}

   	Master_Write_FSM_Reset: coverpoint axi4_lite_master.current_state_write iff (!(bfm.ARESETN)) {    // Coverpoint for Master Write FSM
   	   bins mw_reset1 = (state.ADDR => state.IDLE);
   		bins mw_reset2 = (state.DATA => state.IDLE);
   		bins mw_reset3 = (state.RESP => state.IDLE);
   		illegal_bins mw_illegal1 = (state.IDLE => state.ADDR);
   		illegal_bins mw_illegal2 = (state.ADDR => state.DATA);
   		illegal_bins mw_illegal3 = (state.DATA => state.RESP);
   		illegal_bins mw_illegal4 = (state.DATA => state.ADDR);
   	   illegal_bins mw_illegal5 = (state.RESP => state.DATA);
   	  	illegal_bins mw_illegal6 = (state.RESP => state.ADDR);
   		illegal_bins mw_illegal7 = (state.IDLE => state.DATA);
   		illegal_bins mw_illegal8 = (state.IDLE => state.RESP);
   	   illegal_bins mw_illegal9 = (state.ADDR => state.RESP);
   	}

   	Slave_Read_FSM_Reset: coverpoint axi4_lite_master.current_state_read iff (!(bfm.ARESETN)) {    // Coverpoint for Slave Read FSM
   		bins sr_reset1 = (state.ADDR => state.IDLE);
   		bins sr_reset2 = (state.DATA => state.IDLE);
   		bins sr_reset3 = (state.RESP => state.IDLE);
   		illegal_bins sr_illegal1 = (state.IDLE => state.ADDR);
   		illegal_bins sr_illegal2 = (state.ADDR => state.DATA);
   		illegal_bins sr_illegal3 = (state.DATA => state.RESP);
   		illegal_bins sr_illegal4 = (state.DATA => state.ADDR);
   	   illegal_bins sr_illegal5 = (state.RESP => state.DATA);
   	  	illegal_bins sr_illegal6 = (state.RESP => state.ADDR);
   	   illegal_bins sr_illegal7 = (state.IDLE => state.DATA);
   	   illegal_bins sr_illegal8 = (state.IDLE => state.RESP);
   	   illegal_bins sr_illegal9 = (state.ADDR => state.RESP);
   	}

   	Slave_Write_FSM_Reset: coverpoint axi4_lite_master.current_state_write iff (!(bfm.ARESETN)) {     // Coverpoint for Slave Write FSM
   	   bins sw_reset1 = (state.ADDR => state.IDLE);
   		bins sw_reset2 = (state.DATA => state.IDLE);
   		bins sw_reset3 = (state.RESP => state.IDLE);
   		illegal_bins sw_illegal1 = (state.IDLE => state.ADDR);
   		illegal_bins sw_illegal2 = (state.ADDR => state.DATA);
   		illegal_bins sw_illegal3 = (state.DATA => state.RESP);
   		illegal_bins sw_illegal4 = (state.DATA => state.ADDR);
	   	illegal_bins sw_illegal5 = (state.RESP => state.DATA);
   	  	illegal_bins sw_illegal6 = (state.RESP => state.ADDR);
	   	illegal_bins sw_illegal7 = (state.IDLE => state.DATA);
	   	illegal_bins sw_illegal8 = (state.IDLE => state.RESP);
	   	illegal_bins sw_illegal9 = (state.ADDR => state.RESP);
   	}

endgroup : cg_Reset_Signal


// Function "new" which instantiates all the Covergroups
function new (virtual axi4_lite_bfm i);
      cg_Read_Address = new();
      cg_Read_Data = new();
      cg_Write_Address = new();
      cg_Write_Data = new();
      cg_Write_Response = new();
      cg_Reset_Signal = new();
      cg_CPU_Signals = new();
      cg_Master_FSM = new();
      cg_Slave_FSM = new();

      bfm = i;
endfunction : new


// Task "execute" which samples all the covergroups
// This task can be called in environment class to sample all the covergroups
task execute();
      cg_Read_Address.sample();
      cg_Read_Data.sample();
      cg_Write_Address.sample();
      cg_Write_Data.sample();
      cg_Write_Response.sample();
      cg_Reset_Signal.sample();
      cg_CPU_Signals.sample();
      cg_Master_FSM.sample();
      cg_Slave_FSM.sample();
endtask : execute

endclass

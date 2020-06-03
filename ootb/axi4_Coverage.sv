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


import axi4_lite_Defs::*;


class axi4_Coverage;


covergroup cg_Read_Address();
   Read_Address_Valid: coverpoint ARVALID iff (ARESETN) {
   		bins ARVALID_High = {1};
   		bins ARVALID_Low = {0};
   	}

	Read_Address_Ready: coverpoint ARREADY iff (ARESETN) {
   	   	bins ARREADY_High = {1};
   		bins ARREADY_Low = {0};
   	}

   	Read_Address: coverpoint ARADDR {
   		bins ARADDR_First_Location = {0};
   		wildcard bins ARADDR_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   	   	wildcard bins ARADDR_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}
endgroup : cg_Read_Address


covergroup cg_Read_Data();
   	Read_Data_Valid: coverpoint RVALID iff (ARESETN) {
		bins RVALID_High = {1};
   		bins RVALID_Low = {0};
   	}

	Read_Data_Ready: coverpoint RREADY iff (ARESETN) {
   		bins RREADY_High = {1};
   		bins RREADY_Low = {0};
   	}

   	Read_Data: coverpoint RDATA {
   	   	bins RDATA_All_Zeros = {0};
   		bins RDATA_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   	   	bins RDATA_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_Read_Data


covergroup cg_Write_Address();
   	Write_Address_Valid: coverpoint AWVALID iff (ARESETN) {
	  	bins AWVALID_High = {1};
   		bins AWVALID_Low = {0};
   	}

	Write_Address_Ready: coverpoint AWREADY iff (ARESETN) {
   	  	bins AWREADY_High = {1};
   		bins AWREADY_Low = {0};
   	}

   	Write_Address: coverpoint AWADDR {
   		bins AWADDR_First_Location = {0};
   		wildcard bins AWADDR_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   	   	wildcard bins AWADDR_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}
endgroup : cg_Write_Address


covergroup cg_Write_Data();
   	Write_Data_Valid: coverpoint WVALID iff (ARESETN) {
   		bins WVALID_High = {1};
   		bins WVALID_Low = {0};
   	}

	Write_Data_Ready: coverpoint WREADY iff (ARESETN) {
   		bins WREADY_High = {1};
   		bins WREADY_Low = {0};
   	}

   	Write_Data: coverpoint WDATA {
   	   	bins WDATA_All_Zeros = {0};
   		bins WDATA_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   	   	bins WDATA_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_Write_Data


covergroup cg_Write_Response();
   	Write_Response_Valid: coverpoint BVALID iff (ARESETN) {
   		bins BVALID_High = {1};
   		bins BVALID_Low = {0};
   	}

	Write_Response_Ready: coverpoint BREADY iff (ARESETN) {
   		bins BREADY_High = {1};
   		bins BREADY_Low = {0};
   	}
endgroup : cg_Write_Response


covergroup cg_CPU_Signals();
   	CPU_Read_Enable: coverpoint rd_en {
   		bins rd_en_High = {1};
   		bins rd_en_Low = {0};
   	}

	CPU_Write_Enable: coverpoint wr_en {
   		bins wr_en_High = {1};
   		bins wr_en_Low = {0};
   	}

	CPU_Read_Address: coverpoint Read_Address {
   		bins Read_Address_First_Location = {0};
   		wildcard bins Read_Address_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   	   	wildcard bins Read_Address_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}

	CPU_Write_Address: coverpoint Write_Address {
   		bins Write_Address_First_Location = {0};
   		wildcard bins Write_Address_Last_Location = {32'b????_????_????_????_????_1111_1111_1111};
   	   	wildcard bins Write_Address_range[] = {[32'b1:32'b????_????_????_????_????_1111_1111_1110]};
   	}

	CPU_Write_Data: coverpoint Write_Data {
   		bins Write_Data_All_Zeros = {0};
   		bins Write_Data_All_Ones = {32'b1111_1111_1111_1111_1111_1111_1111_1111};
   	   	bins Write_Data_range[] = {[32'b1:32'b1111_1111_1111_1111_1111_1111_1111_1110]};
   	}
endgroup : cg_CPU_Signals

covergroup cg_Master_FSM();
   	Master_Read_FSM: coverpoint MP.current_state_read iff (ARESETN) {
   		bins mr1 = (IDLE => ADDR);
   		bins mr2 = (ADDR => DATA);
   		bins mr3 = (DATA => RESP);
   		bins mr4 = (RESP => IDLE);
   		bins mr_sequence = (IDLE => ADDR => DATA => RESP => IDLE);
   		illegal_bins mr_illegal1 = (DATA => ADDR);
   	   	illegal_bins mr_illegal2 = (RESP => DATA);
   	  	illegal_bins mr_illegal3 = (RESP => ADDR);
   	   	illegal_bins mr_illegal4 = (IDLE => DATA);
   	   	illegal_bins mr_illegal5 = (IDLE => RESP);
   	   	illegal_bins mr_illegal6 = (ADDR => RESP);
   	}

   	Master_Write_FSM: coverpoint MP.current_state_write iff (ARESETN) {
   	   	bins mw1 = (IDLE => ADDR);
   		bins mw2 = (ADDR => DATA);
   		bins mw3 = (DATA => RESP);
   		bins mw4 = (RESP => IDLE);
   		bins mw_sequence = (IDLE => ADDR => DATA => RESP => IDLE);
   		illegal_bins mw_illegal1 = (DATA => ADDR);
   	   	illegal_bins mw_illegal2 = (RESP => DATA);
   	  	illegal_bins mw_illegal3 = (RESP => ADDR);
   	   	illegal_bins mw_illegal4 = (IDLE => DATA);
   	   	illegal_bins mw_illegal5 = (IDLE => RESP);
   	   	illegal_bins mw_illegal6 = (ADDR => RESP);
   	}
endgroup : cg_Master_FSM

covergroup cg_Slave_FSM();
   	Slave_Read_FSM: coverpoint SP.current_state_read iff (ARESETN) {
   		bins sr1 = (IDLE => ADDR);
   		bins sr2 = (ADDR => DATA);
   		bins sr3 = (DATA => RESP);
   		bins sr4 = (RESP => IDLE);
   		bins sr_sequence = (IDLE => ADDR => DATA => RESP => IDLE);
   		illegal_bins sr_illegal1 = (DATA => ADDR);
   	   	illegal_bins sr_illegal2 = (RESP => DATA);
   	  	illegal_bins sr_illegal3 = (RESP => ADDR);
   	   	illegal_bins sr_illegal4 = (IDLE => DATA);
   	   	illegal_bins sr_illegal5 = (IDLE => RESP);
   	   	illegal_bins sr_illegal6 = (ADDR => RESP);
   	}

   	Slave_Write_FSM: coverpoint SP.current_state_write iff (ARESETN) {
   	   	bins sw1 = (IDLE => ADDR);
   		bins sw2 = (ADDR => DATA);
   		bins sw3 = (DATA => RESP);
   		bins sw4 = (RESP => IDLE);
   		bins sw_sequence = (IDLE => ADDR => DATA => RESP => IDLE);
   		illegal_bins sw_illegal1 = (DATA => ADDR);
   	   	illegal_bins sw_illegal2 = (RESP => DATA);
   	  	illegal_bins sw_illegal3 = (RESP => ADDR);
   	   	illegal_bins sw_illegal4 = (IDLE => DATA);
   	   	illegal_bins sw_illegal5 = (IDLE => RESP);
   	   	illegal_bins sw_illegal6 = (ADDR => RESP);
   	}
endgroup : cg_Slave_FSM

covergroup cg_Reset_Signal();

	Read_Address_Valid_Reset: coverpoint ARVALID iff (!ARESETN) {
   		bins ARVALID_Low_Reset = {0};
   		illegal_bins ARVALID_High_Reset_illegal = {1};
   	}

	Read_Address_Ready_Reset: coverpoint ARREADY iff (!ARESETN) {
   		bins ARREADY_Low_Reset = {0};
   	   	illegal_bins ARREADY_High_Reset_illegal = {1};
   	}

   	Read_Data_Valid_Reset: coverpoint RVALID iff (!ARESETN) {
   		bins RVALID_Low_Reset = {0};
		illegal_bins RVALID_High_Reset_illegal = {1};
   	}

	Read_Data_Ready_Reset: coverpoint RREADY iff (!ARESETN) {
   		bins RREADY_Low_Reset = {0};
   		illegal_bins RREADY_High_Reset_illegal = {1};
   	}

   	Write_Address_Valid_Reset: coverpoint AWVALID iff (!ARESETN) {
   		bins AWVALID_Low_Reset = {0};
	  	illegal_bins AWVALID_High_Reset_illegal = {1};
   	}

	Write_Address_Ready_Reset: coverpoint AWREADY iff (!ARESETN) {
   		bins AWREADY_Low_Reset = {0};
   	  	illegal_bins AWREADY_High_Reset_illegal = {1};
   	}

   	Write_Data_Valid_Reset: coverpoint WVALID iff (!ARESETN) {
   		bins WVALID_Low_Reset = {0};
   		illegal_bins WVALID_High_Reset_illegal = {1};
   	}

	Write_Data_Ready_Reset: coverpoint WREADY iff (!ARESETN) {
   		bins WREADY_Low_Reset = {0};
   		illegal_bins WREADY_High_Reset_illegal = {1};
   	}

   	Write_Response_Valid_Reset: coverpoint BVALID iff (!ARESETN) {
   		bins BVALID_Low_Reset = {0};
   		illegal_bins BVALID_High_Reset_illegal = {1};
   	}

	Write_Response_Ready_Reset: coverpoint BREADY iff (!ARESETN) {
   		bins BREADY_Low_Reset = {0};
   		illegal_bins BREADY_High_Reset_illegal = {1};
   	}

   	Master_Read_FSM_Reset: coverpoint MP.current_state_read iff (!ARESETN) {
   		bins mr_reset1 = (ADDR => IDLE);
   		bins mr_reset2 = (DATA => IDLE);
   		bins mr_reset3 = (RESP => IDLE);
   		illegal_bins mr_illegal1 = (IDLE => ADDR);
   		illegal_bins mr_illegal2 = (ADDR => DATA);
   		illegal_bins mr_illegal3 = (DATA => RESP);
   		illegal_bins mr_illegal4 = (DATA => ADDR);
   	   	illegal_bins mr_illegal5 = (RESP => DATA);
   	  	illegal_bins mr_illegal6 = (RESP => ADDR);
   	   	illegal_bins mr_illegal7 = (IDLE => DATA);
   	   	illegal_bins mr_illegal8 = (IDLE => RESP);
   	   	illegal_bins mr_illegal9 = (ADDR => RESP);

   	}

   	Master_Write_FSM_Reset: coverpoint MP.current_state_write iff (!ARESETN) {
   	   	bins mw_reset1 = (ADDR => IDLE);
   		bins mw_reset2 = (DATA => IDLE);
   		bins mw_reset3 = (RESP => IDLE);
   		illegal_bins mw_illegal1 = (IDLE => ADDR);
   		illegal_bins mw_illegal2 = (ADDR => DATA);
   		illegal_bins mw_illegal3 = (DATA => RESP);
   		illegal_bins mw_illegal4 = (DATA => ADDR);
   	   	illegal_bins mw_illegal5 = (RESP => DATA);
   	  	illegal_bins mw_illegal6 = (RESP => ADDR);
   	   	illegal_bins mw_illegal7 = (IDLE => DATA);
   	   	illegal_bins mw_illegal8 = (IDLE => RESP);
   	   	illegal_bins mw_illegal9 = (ADDR => RESP);
   	}

   	Slave_Read_FSM_Reset: coverpoint SP.current_state_read iff (!ARESETN) {
   		bins sr_reset1 = (ADDR => IDLE);
   		bins sr_reset2 = (DATA => IDLE);
   		bins sr_reset3 = (RESP => IDLE);
   		illegal_bins sr_illegal1 = (IDLE => ADDR);
   		illegal_bins sr_illegal2 = (ADDR => DATA);
   		illegal_bins sr_illegal3 = (DATA => RESP);
   		illegal_bins sr_illegal4 = (DATA => ADDR);
   	   	illegal_bins sr_illegal5 = (RESP => DATA);
   	  	illegal_bins sr_illegal6 = (RESP => ADDR);
   	   	illegal_bins sr_illegal7 = (IDLE => DATA);
   	   	illegal_bins sr_illegal8 = (IDLE => RESP);
   	   	illegal_bins sr_illegal9 = (ADDR => RESP);
   	}

   	   	Slave_Write_FSM_Reset: coverpoint SP.current_state_write iff (!ARESETN) {
   	   	bins sw_reset1 = (ADDR => IDLE);
   		bins sw_reset2 = (DATA => IDLE);
   		bins sw_reset3 = (RESP => IDLE);
   		illegal_bins sw_illegal1 = (IDLE => ADDR);
   		illegal_bins sw_illegal2 = (ADDR => DATA);
   		illegal_bins sw_illegal3 = (DATA => RESP);
   		illegal_bins sw_illegal4 = (DATA => ADDR);
   	   	illegal_bins sw_illegal5 = (RESP => DATA);
   	  	illegal_bins sw_illegal6 = (RESP => ADDR);
   	   	illegal_bins sw_illegal7 = (IDLE => DATA);
   	   	illegal_bins sw_illegal8 = (IDLE => RESP);
   	   	illegal_bins sw_illegal9 = (ADDR => RESP);
   	}

endgroup : cg_Reset_Signal


function execute();

cg_Read_Address cover1 = new;
cg_Read_Data cover2 = new;
cg_Write_Address cover3 = new;
cg_Write_Data cover4 = new;
cg_Write_Response cover5 = new;
cg_CPU_Signals cover6 = new;

cg_Master_FSM coverfsm1 = new;
cg_Slave_FSM coverfsm2 = new;

cg_Reset_Signal coverreset = new;

cover1.sample();
cover2.sample();
cover3.sample();
cover4.sample();
cover5.sample();
cover6.sample();
coverfsm1.sample();
coverfsm2.sample();
coverreset.sample();

endfunction : execute

endclass

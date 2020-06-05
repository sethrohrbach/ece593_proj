/////////////////////////////////////////////////////////////////
// axi4_environment.sv - an environment for the axi4 object oriented testbench.
//
// Author: Seth Rohrbach
// Modified June 5, 2020
//
// Description:
// ------------
//
////////////////////////////////////////////////////////////////




import axi4_lite_Defs::*;


class axi4_environment;

	virtual axi4_lite_bfm bfm;

	axi4_tester tester_h;
	//axi4_Coverage coverage_h;
	axi4_checker checker_h;

	function new (virtual axi4_lite_bfm b);
		bfm = b;
	endfunction : new

	task execute();
		tester_h = new(bfm);
	//	coverage_h = new(bfm);
		checker_h = new(bfm);

		fork
			tester_h.execute();
		//	coverage_h.execute();
			checker_h.execute();
		join_none
	endtask : execute

endclass : axi4_environment

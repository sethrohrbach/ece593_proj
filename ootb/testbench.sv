

class testbench;

	virtual axi4_lite_bfm bfm;

	axi4_tester tester_h;
	axi4_Coverage coverage_h;
	//scoreboard scoreboard_h;

	function new (virtual axi4_lite_bfm b)
		bfm = b;
	endfunction : new

	task execute();
		tester_h = new(bfm);
		coverage_h = new(bfm);
		//scoreboard_h = new(bfm);

		fork
			//tester_h.execute();
			coverage_h.execute();
			//scoreboard_h.execute();
		join_none
	endtask : execute
	
endclass : testbench
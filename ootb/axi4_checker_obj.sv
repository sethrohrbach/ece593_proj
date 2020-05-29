///////////////////////////////////////////////////////////////
// axi4_checker_obj.sv - a simple checker and scoreboard for an object oriented axi4-lite bus testbench.
//
// Author: Seth Rohrbach (rseth@pdx.edu)
// Modified: May 29, 2020
//
// Description:
//------------------------
// A simple checker and scoreboard object for an object oriented AXI4 testbench.
// It will look at the BFM's address lines and the testbench local memory and compare them.
// If the same, yay. If not the same, track a miscompare.
//////////////////////////////////////////////////////////////

import axi4_lite_Defs::*;

class axi4_checker;

  virtual axi4_bfm bfm;

  int score = 0;

  //To store values for comparison:
  logic [Data_Width-1:0] local_mem[4096];

  int i;
  //Set memory to 0 to start...
  for (i = 0; i < 4096; i++) begin
    local_mem[i] = 0;
  end

  //Instantiate the BFM when we create the object.
  function new (virtual axi_bfm b);
    bfm = b;
  endfunction: new

  //Read the write data line and store the value to local memory.
  protected task save_val();
  @(posedge clk);
  //If the WRITE ADDR value is true, we can store the value to local mem.
  if (bfm.AWVALID) begin
    local_mem[bfm.AWADDR] = bfm.WDATA; //So it goes.
  end

  endtask: save_val

  //Read the read value line and check local memory to confirm
  protected task check_val();
  @(posedge clk);
  //If the RVALID is true, then a valid read op is in progress so we can compare.
  if (bfm.RVALID) begin
    //So we just compare it to local mem.
    if (!(bfm.RDATA == local_mem[ARADDR])) begin
      score = score + 1;
    end
  end

  protected task execute();
  int k = 0;
  for (k = 0; k < 4096; k++) begin
    @(posedge clk);
    save_val();
    check_val();



  endtask: check_val

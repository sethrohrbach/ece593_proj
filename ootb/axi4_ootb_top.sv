//////////////////////////////////////////////////////////////////
// axi4_ootb_top.sv - top module to instantiate and execute the object oriented testbench.
//
// Author: Seth Rohrbach (rseth@pdx.edu)
// Modified: June 5, 2020
//
// Description:
// ------------
//
//////////////////////////////////////////////////////////////////


//Packages and includes:
import axi4_lite_Defs::*;
`include "axi4_tb_objs.sv"
`include "axi4_Coverage.sv"
`include "axi4_checker_obj.sv"
`include "axi4_env.sv"


module OOTB_TOP;

  //Local vars:
  bit clk;
  bit rst_N;

  //Object handles:
  axi4_environment env_h;

  //Instantiate the BFM:
  axi4_lite_bfm bfm(.ACLK(clk), .ARSETN(rst_N));

  //Instantiate the DUT master and slave:
  

  //Start the clock:
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //Make object handles, reset, and execute:

  initial begin
    rst_N = 0;
    #20 rst_N = 1;

    env_h = new(bfm)

    env_h.execute();

    $display("Testing finished!");

  end






endmodule : OOTB_TOP

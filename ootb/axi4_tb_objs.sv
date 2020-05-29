////////////////////////////////////////////////////////////////
// axi4_tb_objs.sv - object definitions for an AXI4-Lite bus testbench.
//
// Author: Seth Rohrbach (rseth@pdx.edu)
// Modified: May 29, 2020
//
// Description:
// ------------
// Objects to be used by an object oriented test bench for the AXI4-Lite bus.
//
////////////////////////////////////////////////////////////////

import axi4_lite_Defs::*;

class axi4_tester;

  //Hook the tester up with the AXI4:
  virtual axi4_bfm bfm;


  //To store values for comparison:
  logic [Data_Width-1:0] local_mem[4096];

  int i;
  //Set memory to 0 to start...
  for (i = 0; i < 4096; i++) begin
    local_mem[i] = 0;
  end


  //TB local vars:
  bit wr_en = 0;
  bit rd_en = 0;
  bit clk = 0;

  function new (virtual axi_bfm b);
    bfm = b;
  endfunction: new

//Generate a random address:
  protected function logic gen_addr();
  logic [Addr_Width-1:0] addr = $random;
  return addr;
  endfunction : gen_addr

//Generate a random write value:
  protected function logic gen_data();
  logic [Data_Width-1:0] data = $random;
  return data;
  endfunction : gen_data

  //Write a value out to the light bus and also to local mem.
  protected task rand_write_op();
  @(posedge clk);
  logic [Addr_Width-1:0] write_addr = gen_addr();
  logic [Data_Width-1:0] write_val = gen_data();
  wr_en = 1;
  repeat(5) @(posedge clk);
  wr_en = 0;
  endtask: rand_write_op

  protected task rand_read_op();
  @(posedge clk);
  logic [Addr_Width-1:0] rd_addr = gen_addr();
  logic [Data_Width-1:0] rd_val;
  rd_en = 1;
  repeat(5) @(posedge clk);

  endtask : rand_read_op

  //Let there be clock!
  initial begin
    forever #(10 / 2) clk = ~clk;
  end

  protected task execute();
  int i = 0;
  for (i = 0; i < 4096; i++) begin
    @(posedge clk);
    fork
    rand_write_op();
    rand_read_op();
    join
  end

endclass: axi4_tester

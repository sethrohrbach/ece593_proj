setup:
	vlib work
	vmap work work

compile:
	vlog axi4_lite_Defs.sv
	vlog axi4_lite_if.sv
	vlog axi4_lite_master.sv
	vlog axi4_lite_slave.sv
	vlog axi4_checker_obj.sv
	vlog axi4_Coverage.sv
	vlog axi4_env.sv
	vlog axi4_lite_bfm.sv
	vlog axi4_ootb_top.sv
	vlog axi4_tb_objs.sv
	vopt +acc a_OOTB_TOP -o dut_optimized

run:
	vsim dut_optimized coverage

clean:

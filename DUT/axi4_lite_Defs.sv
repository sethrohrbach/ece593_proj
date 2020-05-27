///////////////////////////////////////////////////////////////////////////
// axi4_lite_Defs.sv - Global definitions for AXI4 Lite Bus
//
// Author: Disha Shetty (dshetty@pdx.edu)
// Date: 18-Mar-2020
//
// Description:
// ------------
// Contains the global definitions such as parameters for the AXI4 Lite bus
///////////////////////////////////////////////////////////////////////////

package axi4_lite_Defs;

parameter

    Addr_Width = 32,                  // Address width of the bus

    Data_Width = 32;                  // Data width of the bus
    
endpackage: axi4_lite_Defs
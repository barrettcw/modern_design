module mem_1r1w (
  clk, rst, ready,
  select_adr,
  read_0,  rd_adr_0, rd_dout_0,
  write_1, wr_adr_1, wr_din_1
);

parameter NUMADDR = 8;
parameter BITADDR = 3;
parameter BITDATA = 1;
parameter SRAM_DELAY = 0;

//Reset init logic.
parameter RSTINIT = 0; 
parameter RSTSTRT = 0;
parameter RSTINCR = 0;

//Used only for formal. 
parameter FORMAL_FULL = 0;

input                 clk;
input                 rst;
output                ready;
input                 read_0;
input  [BITADDR-1:0]  rd_adr_0;
output [BITDATA-1:0]  rd_dout_0;
input                 write_1;
input  [BITADDR-1:0]  wr_adr_1;
input  [BITDATA-1:0]  wr_din_1;
input  [BITADDR-1:0]  select_adr;

`ifdef FORMAL
assign ready = !rst;

wire [BITDATA-1:0] fake_0;
generate if(FORMAL_FULL) begin : full_formal
  reg [BITDATA-1:0] mem [0:NUMADDR-1];
  always @(posedge clk)
    if (rst)
      for (integer i=0; i<NUMADDR; i++)
        mem[i] <= RSTINIT ? RSTSTRT + i*RSTINCR : 'hx;
    else 
      if (write_1)
        mem[wr_adr_1] <= wr_din_1;

  shift #(.BITDATA(BITDATA), .DELAY(SRAM_DELAY)) delay_0(.clk(clk), .din({read_0 ? mem[rd_adr_0] : fake_0}), .dout({rd_dout_0}));
end
else begin : select_formal
  reg [BITDATA-1:0] mem;
  always @(posedge clk)
    if (rst)
      mem <= RSTINIT ? RSTSTRT : 'hx;
    else 
      if (write_1 && (wr_adr_1==select_adr))
        mem <= wr_din_1;

  shift #(.BITDATA(BITDATA), .DELAY(SRAM_DELAY)) delay_0(.clk(clk), .din({(read_0 && rd_adr_0 == select_adr) ? mem : fake_0}), .dout({rd_dout_0}));
end
endgenerate
`endif

endmodule 



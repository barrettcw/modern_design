module mem_2r1w (
  clk, rst, ready,
  select_adr,
  read_0,  rd_adr_0, rd_dout_0,
  read_1,  rd_adr_1, rd_dout_1,
  write_2, wr_adr_2, wr_din_2
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
input                 read_1;
input  [BITADDR-1:0]  rd_adr_1;
output [BITDATA-1:0]  rd_dout_1;
input                 write_2;
input  [BITADDR-1:0]  wr_adr_2;
input  [BITDATA-1:0]  wr_din_2;
input  [BITADDR-1:0]  select_adr;

`ifdef FORMAL
assign ready = !rst;

generate if(FORMAL_FULL) begin : full_formal
  wire [BITDATA-1:0]  rd_dout_0_tmp;
  wire [BITDATA-1:0]  rd_dout_1_tmp;
  reg [BITDATA-1:0] mem [0:NUMADDR-1];
  always @(posedge clk)
    if (rst)
      for (integer i=0; i<NUMADDR; i++)
        mem[i] <= RSTINIT ? RSTSTRT + i*RSTINCR : 'hx;
    else 
      if (write_2)
        mem[wr_adr_2] <= wr_din_2;
  shift #(.BITDATA(2*BITDATA), .DELAY(SRAM_DELAY)) delay_0(.clk(clk), .din({mem[rd_adr_0], mem[rd_adr_1]}), .dout({rd_dout_0_tmp, rd_dout_1_tmp}));
  assume_mem_dout_0_check: assume property (@(posedge clk) disable iff(rst) read_0 |-> ##SRAM_DELAY rd_dout_0 == rd_dout_0_tmp);
  assume_mem_dout_1_check: assume property (@(posedge clk) disable iff(rst) read_1 |-> ##SRAM_DELAY rd_dout_1 == rd_dout_1_tmp);
end
else begin : select_formal
  wire [BITDATA-1:0]  rd_dout_tmp;
  reg [BITDATA-1:0] mem;
  always @(posedge clk)
    if (rst)
      mem <= RSTINIT ? RSTSTRT : 'hx;
    else 
      if (write_2 && (wr_adr_2==select_adr))
        mem <= wr_din_2;

  shift #(.BITDATA(BITDATA), .DELAY(SRAM_DELAY)) delay_0(.clk(clk), .din({mem}), .dout({rd_dout_tmp}));
  assume_mem_dout_0_check: assume property (@(posedge clk) disable iff(rst) read_0 && rd_adr_0==select_adr |-> ##SRAM_DELAY rd_dout_0 == rd_dout_tmp);
  assume_mem_dout_1_check: assume property (@(posedge clk) disable iff(rst) read_1 && rd_adr_1==select_adr |-> ##SRAM_DELAY rd_dout_1 == rd_dout_tmp);
end
endgenerate
`endif

endmodule 



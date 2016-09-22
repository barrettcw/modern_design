module atom_2r2w (
  clk, rst, ready,
  select_adr,
  read_0,  rd_adr_0, rd_dout_0,
  read_1,  rd_adr_1, rd_dout_1,
  write_2, wr_adr_2, wr_din_2,
  write_3, wr_adr_3, wr_din_3
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
input                 write_3;
input  [BITADDR-1:0]  wr_adr_3;
input  [BITDATA-1:0]  wr_din_3;
input  [BITADDR-1:0]  select_adr;

`ifdef FORMAL
assign ready = !rst;

wire [BITDATA-1:0] fake_0, fake_1;
wire               read_0_del, read_1_del;
wire [BITADDR-1:0] rd_adr_0_del, rd_adr_1_del;
shift #(.BITDATA(1+BITADDR), .DELAY(SRAM_DELAY)) delay_0(.clk(clk), .din({read_0,rd_adr_0}), .dout({read_0_del,rd_adr_0_del}));
shift #(.BITDATA(1+BITADDR), .DELAY(SRAM_DELAY)) delay_1(.clk(clk), .din({read_1,rd_adr_1}), .dout({read_1_del,rd_adr_1_del}));

generate if(FORMAL_FULL) begin : full_formal
  reg [BITDATA-1:0] mem [0:NUMADDR-1];
  always @(posedge clk)
    if (rst)
      for (integer i=0; i<NUMADDR; i++)
        mem[i] <= RSTINIT ? RSTSTRT + i*RSTINCR : 'hx;
    else begin
      if (write_2) mem[wr_adr_2] <= wr_din_2;
      if (write_3) mem[wr_adr_3] <= wr_din_3;
    end
  assign rd_dout_0 = read_0_del ? mem[rd_adr_0_del] : fake_0;
  assign rd_dout_1 = read_1_del ? mem[rd_adr_1_del] : fake_1;
end
else begin : select_formal
  reg [BITDATA-1:0] mem;
  always @(posedge clk)
    if (rst)
      mem <= RSTINIT ? RSTSTRT : 'hx;
    else begin
      if (write_2 && (wr_adr_2==select_adr)) mem <= wr_din_2;
      if (write_3 && (wr_adr_3==select_adr)) mem <= wr_din_3;
    end
  assign rd_dout_0 = (read_0_del && (rd_adr_0_del==select_adr)) ? mem : fake_0;
  assign rd_dout_1 = (read_1_del && (rd_adr_1_del==select_adr)) ? mem : fake_1;
end
endgenerate

`endif

endmodule 



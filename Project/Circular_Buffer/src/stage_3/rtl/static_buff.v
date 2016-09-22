module static_buff(
  clk, rst, ready,
  push, pu_prt, pu_din,
  pop, po_prt, po_dout
);

parameter NUMELEM = 4;    //Number of elements in FIFO 
parameter BITDATA = 4;    //Width of the elements in FIFO
parameter NUMFIFO = 8;    //Number of FIFOs

localparam BITELEM = $clog2(NUMELEM);
localparam NUMADDR = NUMFIFO*NUMELEM;
localparam BITADDR = $clog2(NUMADDR);
localparam BITFIFO = $clog2(NUMFIFO);

input                clk;
input                rst;
output               ready;

input                push;
input  [BITFIFO-1:0] pu_prt;
input  [BITDATA-1:0] pu_din;

input                pop;
input  [BITFIFO-1:0] po_prt;
output [BITDATA-1:0] po_dout;

wire [BITFIFO-1:0] select_prt;

wire head_ready, cnt_ready, data_ready;
assign ready = head_ready && cnt_ready && data_ready;

wire [BITELEM-1:0] pu_head;
wire [BITELEM-1:0] po_head;
mem_2r1w #(.NUMADDR(NUMFIFO), .BITADDR(BITFIFO), .BITDATA(BITELEM), .RSTINIT(1))
  head_inst (.clk(clk), .rst(rst), .ready(head_ready), .select_adr(select_prt),
             .read_0(push), .rd_adr_0(pu_prt), .rd_dout_0(pu_head),
             .read_1(pop),  .rd_adr_1(po_prt), .rd_dout_1(po_head),
             .write_2(pop), .wr_adr_2(po_prt), .wr_din_2((po_head+1)%NUMELEM));


wire conflict = push && pop && (pu_prt == po_prt);
wire [BITELEM  :0] pu_cnt;
wire [BITELEM  :0] po_cnt;
mem_2r2w #(.NUMADDR(NUMFIFO), .BITADDR(BITFIFO), .BITDATA(BITELEM+1), .RSTINIT(1))
  cnt_inst (.clk(clk), .rst(rst), .ready(cnt_ready), .select_adr(select_prt),
             .read_0(push),  .rd_adr_0(pu_prt), .rd_dout_0(pu_cnt),
             .read_1(pop),   .rd_adr_1(po_prt), .rd_dout_1(po_cnt),
             .write_2(push && !conflict), .wr_adr_2(pu_prt), .wr_din_2(pu_cnt+1),
             .write_3(pop  && !conflict), .wr_adr_3(po_prt), .wr_din_3(po_cnt-1));


wire [BITELEM-1:0] pu_tail = (pu_head+pu_cnt)%NUMELEM;

mem_1r1w #(.NUMADDR(NUMADDR), .BITADDR(BITADDR), .BITDATA(BITDATA), .FORMAL_FULL(1))
  data_inst (.clk(clk), .rst(rst), .ready(data_ready),
             .read_0(pop), .rd_adr_0(po_prt*NUMELEM+po_head), .rd_dout_0(po_dout),
             .write_1(push), .wr_adr_1(pu_prt*NUMELEM+pu_tail), .wr_din_1(pu_din));



`ifdef FORMAL

reg [BITDATA-1:0] ref_fifo [0:NUMELEM-1];
reg [BITELEM  :0] ref_cnt;

reg [BITDATA-1:0] ref_fifo_nxt[0:NUMELEM-1];
reg [BITELEM  :0] ref_cnt_nxt;

always @(posedge clk)
  if(rst)
    ref_cnt <= 0;
  else begin
    ref_cnt <= ref_cnt_nxt;
    for(integer i=0; i<NUMELEM; i=i+1)
      ref_fifo[i] <= ref_fifo_nxt[i];
  end

always_comb begin
  ref_cnt_nxt = ref_cnt;
  for(integer i=0; i<NUMELEM; i=i+1)
    ref_fifo_nxt[i] = ref_fifo[i];
  
  if(pop && po_prt==select_prt) begin
    ref_cnt_nxt = ref_cnt_nxt -1;
    for(integer i=0; i<NUMELEM-1; i=i+1) 
      ref_fifo_nxt[i] = ref_fifo_nxt[i+1];
  end
  if(push && pu_prt==select_prt) begin
    for(integer i=0; i<NUMELEM; i=i+1)
      if(i == ref_cnt_nxt)
        ref_fifo_nxt[i] = pu_din;
    ref_cnt_nxt = ref_cnt_nxt + 1;
  end
end
assume_select_prt_stable_check: assert property (@(posedge clk) disable iff(rst) $stable(select_prt) && select_prt < NUMFIFO);
assume_pop_en_check: assert property (@(posedge clk) disable iff(rst) pop && po_prt==select_prt |-> (ref_cnt > 0)); 
assume_push_en_check: assert property (@(posedge clk) disable iff(rst) push && pu_prt==select_prt |-> (ref_cnt < NUMELEM)); 

assert_po_dout_check: assert property (@(posedge clk) disable iff(rst) pop && po_prt == select_prt |-> po_dout == ref_fifo[0]); 

`endif

endmodule

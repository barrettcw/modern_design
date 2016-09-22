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


reg [BITELEM-1:0] head [0:NUMFIFO-1];
reg [BITELEM  :0] cnt  [0:NUMFIFO-1];
reg [BITELEM-1:0] head_nxt [0:NUMFIFO-1];
reg [BITELEM  :0] cnt_nxt  [0:NUMFIFO-1];

always @(posedge clk)
  for(integer i=0; i<NUMFIFO; i=i+1)
    if(rst) begin
      cnt[i] <= 0;
      head[i] <= 0;
    end
    else begin
      cnt[i] <= cnt_nxt[i];
      head[i] <= head_nxt[i];
    end

always_comb begin
  for(integer i=0; i<NUMFIFO; i=i+1) begin
    cnt_nxt[i] = cnt[i];
    head_nxt[i] = head[i];
  end
  if(push) begin
    cnt_nxt[pu_prt] = cnt_nxt[pu_prt]+1;
  end
  if(pop) begin
    cnt_nxt[po_prt] = cnt_nxt[po_prt]-1;
    head_nxt[po_prt] = (head_nxt[po_prt]+1)%NUMELEM;
  end
end

wire [BITELEM-1:0] pu_tail = (cnt[pu_prt]+head[pu_prt])%NUMELEM;
wire [BITADDR-1:0] pu_addr = pu_prt*NUMELEM + pu_tail;

reg  [BITDATA-1:0] data_mem [0:NUMADDR-1];
always @(posedge clk)
  if(push)
    data_mem[pu_addr] <= pu_din;
 
wire [BITELEM-1:0] po_head = head[po_prt];
wire [BITADDR-1:0] po_addr = po_prt*NUMELEM + po_head;
assign po_dout = data_mem[po_addr];


`ifdef FORMAL
wire [BITFIFO-1:0] select_prt;

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

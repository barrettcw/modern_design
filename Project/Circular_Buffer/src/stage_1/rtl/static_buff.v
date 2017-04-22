module static_buff(
  clk, rst, ready,
  push, pu_din,
  pop, po_dout
);

parameter NUMELEM = 4;    //Number of elements in FIFO 
parameter BITDATA = 4;    //Width of the elements in FIFO

localparam BITELEM = $clog2(NUMELEM);

input                clk;
input                rst;
output               ready;

input                push;
input  [BITDATA-1:0] pu_din;

input                pop;
output [BITDATA-1:0] po_dout;


reg [BITELEM-1:0] head;
reg [BITELEM  :0] cnt;

always @(posedge clk)
  if(rst) begin
    cnt <= 0;
    head <= 0;
  end
  else begin
    cnt <= cnt - pop + push;
    head <= (head + pop)%NUMELEM;
  end

wire [BITELEM-1:0] tail = (cnt+head)%NUMELEM;

reg  [BITDATA-1:0] data_mem [0:NUMELEM-1];
always @(posedge clk)
  if(push)
    data_mem[tail] <= pu_din;
 
assign po_dout = data_mem[head];


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
  
  if(pop) begin
    ref_cnt_nxt = ref_cnt_nxt -1;
    for(integer i=0; i<NUMELEM-1; i=i+1) 
      ref_fifo_nxt[i] = ref_fifo_nxt[i+1];
  end
  if(push) begin
    for(integer i=0; i<NUMELEM; i=i+1)
      if(i == ref_cnt_nxt)
        ref_fifo_nxt[i] = pu_din;
    ref_cnt_nxt = ref_cnt_nxt + 1;
  end
end

assume_pop_en_check: assume property (@(posedge clk) disable iff(rst) pop |-> (ref_cnt > 0)); 
assume_push_en_check: assume property (@(posedge clk) disable iff(rst) push |-> (ref_cnt < NUMELEM)); 

assert_po_dout_check: assert property (@(posedge clk) disable iff(rst) pop |-> po_dout == ref_fifo[0]); 

`endif

endmodule

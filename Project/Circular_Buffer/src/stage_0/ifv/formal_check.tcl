clock -add clk -initial 0
force rst 1
run 10
force rst 0
run 10
init -load -current
init -show
define effort 1 minutes
define engine_profile on
define engine auto_dist
assertion -delete -all
constraint -delete -all
cutpoint -show -all
constraint -show -all
assertion -add static_buff.assert_po_dout_check
assertion -show -all
prove

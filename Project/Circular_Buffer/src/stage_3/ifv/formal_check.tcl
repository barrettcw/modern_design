clock -add clk -initial 0
force rst 1
run 10
force rst 0

init -load -current
init -show

define effort 1 minutes
define engine_profile on
define engine auto_dist

assertion -delete -all
constraint -delete -all

#Add cutpoint
cutpoint -show -all
constraint -add -pin rst 0

constraint -add static_buff.assume_select_prt_stable_check
constraint -add static_buff.assume_pop_en_check
constraint -add static_buff.assume_push_en_check
constraint -show -all

assertion -add static_buff.assert_po_dout_check
assertion -show -all

prove

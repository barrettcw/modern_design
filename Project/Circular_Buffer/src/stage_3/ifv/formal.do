onerror {exit 1}
do directive.do
configure error -inferred black_box
formal compile -d static_buff
formal verify -init init.seq -timeout 1m
exit 0

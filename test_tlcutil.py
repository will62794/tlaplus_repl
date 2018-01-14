import tlcutil

""" Simple tests of TLA+ expression evaluation using TLC. """

def test_eval(tla_expr, expected):
	tlcutil.prepare_tla_eval(tla_expr)
	ret = tlcutil.tlc_eval(tla_expr)
	assert ret["result"]==expected

test_eval("2+2", "4")
test_eval("{x*2 : x \\in {1,2,3}}", "{2, 4, 6}")
test_eval("CHOOSE x \\in {1,2,3} : x>2", "3")

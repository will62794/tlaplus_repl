from subprocess import check_output

""" Utility functions for evaluating a TLA+ expression using the TLC model checker """

tla_spec_template = open("REPLSpec_Template.tla").read()

def prepare_tla_eval(expr):
	out_spec_name = "REPLSpec"
	tla_eval_spec = tla_spec_template % (out_spec_name, expr)
	spec_file = open(out_spec_name+".tla", 'w')
	spec_file.write(tla_eval_spec)
	spec_file.close()

def tlc_eval(expr):
	""" Run TLC to evaluate a TLA+ expression. """
	args = ["-deadlock", "-config", "MC.cfg", "REPLSpec.tla"]
	raw_out = check_output(["java", "tlc2.TLC"] + args)
	lines = raw_out.split("\n")
	try:
		start = lines.index("\"TLAREPL_START\"")
		end = lines.index("\"TLAREPL_END\"")
		repl_lines = lines[start+1:end]
		expr_res = "\n".join(repl_lines)
		return {"raw_output": raw_out, "result": expr_res}
	except Exception as e:
		return None
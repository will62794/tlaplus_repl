import subprocess
from subprocess import check_output

""" Utility functions for evaluating a TLA+ expression using the TLC model checker """

# TLA+ Spec template that lets us evaluate and print arbitary expressions using TLC.
tla_spec_template = """
------------------------- MODULE %s -------------------------
EXTENDS Naturals, Sequences, Bags, FiniteSets, TLC
ASSUME  /\ PrintT("TLAREPL_START")
	    /\ PrintT(%s)
	    /\ PrintT("TLAREPL_END")
============================================================================= """

tlc_temp_dir = "tlarepl"
temp_spec_name = "REPLSpec"

def prepare_tla_eval(expr):
	""" Creates a TLA+ spec that, when run with TLC prints the evaluation of the given expression 'expr'. """
	# Make spec file to evaluate and print given expression.
	tla_eval_spec = tla_spec_template % (temp_spec_name, expr)
	spec_file = open(("%s.tla" % temp_spec_name), 'w')
	spec_file.write(tla_eval_spec)
	spec_file.close()

	# Make dummy TLC config file
	cfg_file = open("MC.cfg", 'w')
	cfg_file.write("")
	cfg_file.close

def tlc_eval(expr):
	""" Run TLC to evaluate a TLA+ expression. """
	args = ["-deadlock", "-config", "MC.cfg", ("%s.tla" % temp_spec_name)]
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


from subprocess import check_output, Popen, PIPE

""" Utility functions for evaluating a TLA+ expression using the TLC model checker """

# TLA+ Spec template that lets us evaluate and print arbitary expressions using TLC.
tla_spec_template = """
------------------------- MODULE %s -------------------------
EXTENDS Naturals, Reals, Sequences, Bags, FiniteSets, TLC
%s
ASSUME  /\ PrintT("TLAREPL_START")
	    /\ PrintT(%s)
	    /\ PrintT("TLAREPL_END")
============================================================================= """

tlc_temp_dir = "tlarepl"
temp_spec_name = "REPLSpec"
temp_cfg_name = "MC"

def tmp_spec_path(tmpdir):
	""" Return the path of the temporary TLA spec file. """
	return "%s/%s.tla" % (tmpdir, temp_spec_name)	

def tmp_cfg_path(tmpdir):
	""" Return the path of the temporary TLC config  file. """
	return "%s/%s.cfg" % (tmpdir, temp_cfg_name)

def prepare_tla_eval(tmpdir, context, expr):
	""" Creates a TLA+ spec that, when run with TLC prints the evaluation of the given expression 'expr'. 
	The given 'context' is a dictionary mapping definition names to their expressions, as strings."""
	
	# Make spec file to evaluate and print given expression.
	context_str = " ".join(context.values())
	tla_eval_spec = tla_spec_template % (temp_spec_name, context_str, expr)
	spec_file = open(tmp_spec_path(tmpdir), 'w')
	spec_file.write(tla_eval_spec)
	spec_file.close()

	# Make dummy TLC config file
	cfg_file = open(tmp_cfg_path(tmpdir), 'w')
	cfg_file.write("")
	cfg_file.close

def tlc_eval(tmpdir, expr):
	""" Run TLC to evaluate a TLA+ expression. """

	# Run TLC from inside the temp directory and capture the output.
	args = ["-deadlock", "-config", ("%s.cfg" % temp_cfg_name), temp_spec_name]
	process = Popen(["java", "tlc2.TLC"] + args, stdout=PIPE, stderr=PIPE, cwd=tmpdir)
	stdout, stderr = process.communicate()
	lines = str.splitlines(stdout)
	try:
		start = lines.index("\"TLAREPL_START\"")
		end = lines.index("\"TLAREPL_END\"")
		repl_lines = lines[start+1:end]
		expr_res = "\n".join(repl_lines)
		return {"raw_output": stdout, "result": expr_res}
	except Exception as e:
		return None


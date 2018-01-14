from subprocess import check_output
import cmd

tla_spec_template = open("REPLSpec_Template.tla").read()

def prepare_tla_eval(expr):
	out_spec_name = "REPLSpec"
	tla_eval_spec = tla_spec_template % (out_spec_name, expr)
	spec_file = open(out_spec_name+".tla", 'w')
	spec_file.write(tla_eval_spec)
	spec_file.close()

def tlc_eval(expr):
	""" Run TLC to evaluate a TLA+ expression. """
	args = ["-deadlock", "-config", "MC.cfg", "MC.tla"]
	raw_out = check_output(["java", "tlc2.TLC"] + args)
	lines = raw_out.split("\n")
	start =  lines.index("\"TLAREPL_START\"")
	end = lines.index("\"TLAREPL_END\"")
	try:
		repl_lines = lines[start+1:end]
		return "\n".join(repl_lines)
	except:
		return None


intro_text = """ -------\nWelcome to the TLA+ REPL! This REPL uses the TLC model checker
to evaluate TLA+ expressions interactively. It is meant as an
aid for learning TLA+ and debugging TLA+ specs.\n-------"""

class TLARepl(cmd.Cmd):
    """TLA+ REPL that uses TLC to evaluate expressions."""

    prompt = '(TLA+REPL) '
    intro = intro_text

    def default(self, expr):
    	prepare_tla_eval(expr)
        ret = tlc_eval(expr)
        if ret:
        	print ret
        else:
        	print "Error evaluating expression '" + expr + "'"
        return False

    def completedefault(self, text, line, begidx, endidx):
    	print text
    	return ["willy", "bob"]

    def do_EOF(self, line):
    	print "EOF"
        return True

replCmd = TLARepl()
replCmd.cmdloop()


import cmd

from tlcutil import prepare_tla_eval, tlc_eval

intro_text = """ -------\nWelcome to the TLA+ REPL! This REPL uses the TLC model checker
to evaluate TLA+ expressions interactively. It is meant as an
aid for learning TLA+ and debugging TLA+ specs.\n-------"""

class TLARepl(cmd.Cmd):
    """TLA+ REPL that uses TLC to evaluate expressions."""

    prompt = '(TLA+REPL) >>> '
    intro = intro_text

    def default(self, expr):
    	prepare_tla_eval(expr)
        ret = tlc_eval(expr)
        if ret:
        	print ret["result"]
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


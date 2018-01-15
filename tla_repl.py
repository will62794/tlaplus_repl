import cmd

from tlcutil import prepare_tla_eval, tlc_eval

intro_text = ("-" * 85 + "\n")
intro_text += """ Welcome to the TLA+ REPL! This REPL uses the TLC model checker
 to evaluate TLA+ expressions interactively. It is meant as an
 aid for learning TLA+ and debugging TLA+ specs."""
intro_text += ("\n" + "-" * 85)

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

    def do_quit(self, expr):
        # Exit the REPL loop.
        print "Goodbye!"
        return True


if __name__ == '__main__':
    # Run the TLA+ REPL.
    replCmd = TLARepl()
    replCmd.cmdloop()


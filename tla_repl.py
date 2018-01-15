import cmd
from tlcutil import prepare_tla_eval, tlc_eval

""" REPL for the TLA+ language. Uses the TLC model checker to evaluate
expressions, so you will need to have the TLA+ tools downloaded and in your
CLASSPATH. You can test to see if you do by running the following command and
checking for a similar output:

    % java tlc2.TLC                                                                                                                                      !10164
    TLC2 Version 2.11 of 05 January 2018
    Error: Error: Missing input TLA+ module.
    Usage: java tlc2.TLC [-option] inputfile

Once you have the tools set up, you can start up the REPL:

    python tla_repl.py

"""


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
        """ The default expression handler. """
        try:
            prepare_tla_eval(expr)
            ret = tlc_eval(expr)
        except Exception as e:
            print e
            print "Make sure you have the TLA+ Tools directory in your CLASSPATH."
            return False

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


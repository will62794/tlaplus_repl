import cmd
import tempfile
import re
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

    def __init__(self, tmpdir):
        cmd.Cmd.__init__(self)
        self.prompt = "(TLA+REPL) >>> "
        self.intro  = intro_text
        # Directory to store tempfiles used for TLC expression evaluation.
        self.tmpdir = tmpdir
        # The context for evaluating TLA+ repl expressions. It is initially empty.
        # It can grow as new definitions are created in a repl session.
        self.context = {}

    def default(self, expr):
        """ The default expression handler. """
        try:
            # See if this is a new definition i.e. something like 'var == {1,2,3}'
            # In that case, don't evaluate it, just add it to the context. Note that
            # '\S' in a regex matches any non whitespace character.
            regex = "(?P<def>\S+)( )?==.*"
            m = re.match(regex, expr)
            if m:
                # Overwrite an existing definition if there is a name conflict.
                self.context[m.group("def")] = expr
                return False

            # Evaluate the given expression.
            prepare_tla_eval(self.tmpdir, self.context, expr)
            ret = tlc_eval(self.tmpdir, expr)
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
    # Create a temp directory to store TLA+ and TLC config files.
    tmpdir = tempfile.mkdtemp()

    # Run the TLA+ REPL.
    replCmd = TLARepl(tmpdir)
    replCmd.cmdloop()


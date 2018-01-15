# TLA+ REPL

This is a Python based REPL for evaluating TLA+ expressions. It provides an easy, interactive way to debug TLA+ expressions and can help when learning or experimenting with the language. It uses the TLC model checker to evaluate TLA+ expressions.

Usage:

```
$ python tla_repl.py
```

Demo:

[![asciicast](https://asciinema.org/a/l5U3vkqaGSvsYaR3UNVzL3WA3.png)](https://asciinema.org/a/l5U3vkqaGSvsYaR3UNVzL3WA3)

The evaluation of expressions in the interactive REPL is a bit slow, since it starts up a new instance of the TLC model checker each time. It also does not yet support any persistence within the same REPL session. That is, each expression is evaluated in isolation, and so earlier definitions will not be used in later expressions. The feedback loop for experimentation is still considerably better than what is currently provided by the TLA+ Toolbox IDE. Eventually TLC may support some kind of "interactive" mode natively, which would make it much easier to build a performant and robust REPL.

# Setup

In order to use the REPL, you must have the TLA+ tools installed and they must be present in your `CLASSPATH` environment variable. There is a helper script that will download the tools and add their directory to your `CLASSPATH` environment for the current running shell. You can run:

```
source setup_tlc.sh
```

to set up the tools. After that, you should be able to start up the REPL and it should work correctly. You can always test if you have the TLA+ tools installed correctly by running the following command, which invokes the TLC model checker: 

```
$ java tlc2.TLC
```

You should get an output like the following:

```
TLC2 Version 2.11 of 05 January 2018
Error: Error: Missing input TLA+ module.
Usage: java tlc2.TLC [-option] inputfile
```
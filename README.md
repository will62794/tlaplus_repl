# TLA+ REPL

**August 2023 Update**: In addition to the [REPL](https://github.com/tlaplus/tlaplus/blob/0e41129ebaf346dd6b2ee46a9dc977aaf954a2d0/tlatools/org.lamport.tlatools/src/tlc2/REPL.java) that is now included in TLC, see also the [web-based REPL prototype](https://will62794.github.io/tla-web/#!/home?specpath=./specs/repl.tla&repl=true), which provides most of the same functionality with faster evaluation speed and without a need to install any TLA+ tools locally.

**June 2020 Update**: The [newest versions](https://github.com/tlaplus/tlaplus/commit/97afa3c6952e343ee2409366a668ba12afceeef4) of TLC include a built in REPL that provides most of the same functionality provided in this Python tool with considerably lower evaluation latency. You can use it by running `java -cp tla2tools.jar tlc2.REPL` from the command line.

----

This is a Python based REPL for evaluating TLA+ expressions. It provides an easy, interactive way to debug TLA+ expressions and can help when learning or experimenting with the language. It uses the TLC model checker to evaluate TLA+ expressions.

Usage:

```
$ python tla_repl.py
```

Here is an example of evaluating expressions in a REPL session:

```
-------------------------------------------------------------------------------------
 Welcome to the TLA+ REPL! This REPL uses the TLC model checker
 to evaluate TLA+ expressions interactively. It is meant as an
 aid for learning TLA+ and debugging TLA+ specs.
-------------------------------------------------------------------------------------
(TLA+REPL) >>> 2 + 2
4
(TLA+REPL) >>> {1,2,3} \X {3,4,5}
{ <<1, 3>>,
  <<1, 4>>,
  <<1, 5>>,
  <<2, 3>>,
  <<2, 4>>,
  <<2, 5>>,
  <<3, 3>>,
  <<3, 4>>,
  <<3, 5>> }
(TLA+REPL) >>> CHOOSE x \in {1,2,3,4} : x > 2
3
(TLA+REPL) >>> S == {1,2,3}
(TLA+REPL) >>> T == {4,5,6}
(TLA+REPL) >>> S \cup T
{1, 2, 3, 4, 5, 6}
(TLA+REPL) >>> quit
Goodbye!
```

Note that you can define variables that can be used later on in the session, by using the standard TLA+ syntax for definitions i.e. `var == <some_expr>`.

The evaluation of expressions in the interactive REPL is a bit slow, since it starts up a new instance of the TLC model checker each time. The feedback loop for experimentation is still considerably better than what is currently provided by the TLA+ Toolbox IDE. Eventually TLC may support some kind of "interactive" mode natively, which would make it much easier to build a performant and robust REPL.

# Setup

In order to use the REPL, you must have the TLA+ tools installed and they must be present in your `CLASSPATH` environment variable. There is a helper script that will download the tools and add their directory to your `CLASSPATH` for the current running shell. You can run:

```
$ source setup_tlc.sh
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

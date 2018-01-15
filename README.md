# TLA+ REPL

This is a Python based REPL for evaluating TLA+ expressions. It provides an easy, interactive way to debug TLA+ expressions and can help when learning or experimenting with TLA+. It uses the TLC model checker to evaluate TLA+ expressions.

Usage:

```
python tla_repl.py
```

The evaluation of expressions in the interactive REPL is a bit slow, since it just starts up a new run of the TLC model checker each time. The feedback loop is still considerably better than what is currently provided by the TLA+ Toolbox IDE. Eventually TLC may support some kind of 'interactive' mode natively, which would make it much easier to build a performant and robust REPL.
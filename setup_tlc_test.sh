#!/bin/sh
echo "Removing old directory and clearing CLASSPATH"
rm -rf tlatools
unset CLASSPATH
echo "Original CLASSPATH: $CLASSPATH"
source setup_tlc.sh
echo "New CLASSPATH: $CLASSPATH"
java tlc2.TLC


#!/bin/sh

#
# This script will download the TLA+ tools to the current directory.
# After downloading it will also add the tools directory to your CLASSPATH
# environment so that you can run the tools from the command line. If you want
# the directory in your CLASSPATH permanently, you will have to add it to your
# shell startup script i.e. .bashrc, .zshrc, etc.
#
# Usage:
#
#	source setup_tlc.sh
#

tla_tools_dir="tlatools"
tla_tools_link="https://tla.msr-inria.inria.fr/tlatoolbox/dist/tla.zip"
tla_tools_zip="tla.zip"

# Download and unzip TLA+ Tools.
mkdir -p tlatools
curl -o "$tla_tools_dir/$tla_tools_zip" $tla_tools_link
unzip "$tla_tools_dir/$tla_tools_zip" -d "$tla_tools_dir"

# Set Java CLASSPATH correctly.
export CLASSPATH=$CLASSPATH:"$(pwd)/tlatools/tla"
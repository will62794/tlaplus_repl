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
echo "Downloading the TLA+ tools from '$tla_tools_link'."
curl -s -o "$tla_tools_dir/$tla_tools_zip" $tla_tools_link
echo "Unpacking the TLA+ tools."
unzip -q -o "$tla_tools_dir/$tla_tools_zip" -d "$tla_tools_dir"

# Set Java CLASSPATH correctly.
export CLASSPATH=$CLASSPATH:"$(pwd)/tlatools/tla"

echo "Added '$(pwd)/tlatools/tla' to the CLASSPATH environment variable."
echo "Setup complete! Check that the TLA+ tools were installed by running 'java tlc2.TLC'."

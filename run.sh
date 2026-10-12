#!/bin/sh

xmake f -c -m debug
xmake project -y -k compile_commands build
xmake
xmake run test

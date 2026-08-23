#!/bin/sh

xmake f -c
xmake project -y -k compile_commands build
xmake
xmake run test

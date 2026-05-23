#!/bin/sh

xmake project -y -k compile_commands build
xmake
xmake run test

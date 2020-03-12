#!/bin/bash

clang=resultclang.c
cli=resultcli.c

$sparrow -il -frontend clang $1 > $clang
$sparrow -il -frontend cli $1 > $cli

vim -c o $1 -c "vsp $clang" -c "sp $cli"

#!/bin/bash
$sparrow -il -frontend clang $1 > resultclang
$sparrow -il -frontend cli $1 > resultcli

vim -c o $1 -c "vsp resultclang" -c "sp resultcli"

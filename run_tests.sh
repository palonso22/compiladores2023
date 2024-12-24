#!/bin/bash

# Specify the folder path you want to iterate through
folder="tests/ok/11-sugar/"

make test_all

rm $folder*.check_*
rm $folder*.actual_out_*
rm $folder*.bc32
rm $folder*.c

#!/bin/bash

# Specify the folder path you want to iterate through
folder="tests/ok/10-sugar/"

make test_all

rm $folder*.check_*
rm $folder*.actual_out_*
rm $folder*.bc32

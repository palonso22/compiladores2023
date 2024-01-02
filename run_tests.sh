#!/bin/bash

# Specify the folder path you want to iterate through
folder="tests/ok/10-sugar/"

rm $folder*.check_eval
rm $folder*.actual_out_eval

make test_all


#!/bin/sh

rm -f export/c/Decode.c export/c/Decode.o export/py/Decode.py export/py/Decode.out

make export/c/Decode.o export/py/Decode.out

# cat export/c/Decode.c
# cat export/py/Decode.py

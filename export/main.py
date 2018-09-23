import json
import sys
from CPrinter import CPrinter
from PythonPrinter import PythonPrinter
from translate import translate

if len(sys.argv) != 3:
    print("Usage: exactly two args: input file to translate (json) and output file")
    sys.exit(1)

inpath = sys.argv[1]
outpath = sys.argv[2]

with open(inpath, 'r') as fin, open(outpath, 'w') as fout:
    if outpath[-2:] == '.h':
        printer = CPrinter(fout)
    elif outpath[-3:] == '.py':
        printer = PythonPrinter(fout)
    else:
        raise ValueError("Output file '{}' has an unknown file extension".format(outpath))

    j = json.load(fin)
    translate(j, printer)

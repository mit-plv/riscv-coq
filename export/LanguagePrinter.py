import sys

class LanguagePrinter(object):
    def __init__(self, outfile):
        self.outfile = outfile
        self.indent = ''

    def write(self, text):
        self.outfile.write(text)

    def writeln(self, line):
        self.outfile.write(self.indent + line + '\n')

    def flush(self):
        self.outfile.flush()

    def startln(self):
        self.outfile.write(self.indent)

    def increaseIndent(self):
        self.indent = self.indent + '    '

    def decreaseIndent(self):
        self.indent = self.indent[:-4]

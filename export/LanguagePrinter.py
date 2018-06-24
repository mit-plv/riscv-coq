
class LanguagePrinter(object):
    def __init__(self, outfile):
        self.outfile = outfile
        self.indent = ''
        
    def writeln(self, line):
        self.outfile.write(self.indent + line + '\n')

    def increaseIndent(self):
        self.indent = self.indent + '    '

    def decreaseIndent(self):
        self.indent = self.indent[:-4]

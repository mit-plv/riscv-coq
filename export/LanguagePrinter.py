
class LanguagePrinter(object):
    def __init__(self, outfile):
        self.outfile = outfile
        
    def writeln(self, line):
        self.outfile.write(line + '\n')

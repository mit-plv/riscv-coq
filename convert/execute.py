import re


def read_coq_template(filepath):
    prefix = ""
    suffix = ""
    with open(filepath) as f:
        is_before = True
        is_after = False
        for line in f:
            if is_before:
                prefix += line
            if line.rstrip() == "    (* begin ast *)":
                is_before = False
            elif line.rstrip() == "    (* end ast *)":
                is_after = True
            if is_after:
                suffix += line
    return (prefix, suffix)


casename = ""

blacklist = r'^(S.)$'

# blacklist = r'^(FirstInstructionToCommentOut|SecondInstruction|Etc)$'

def convert_line(line):
    global casename

    extra_indent = "  "

    line = re.sub(r'^(.*<-.*)$', r'\1;', line)
    line = re.sub(r'^(\s*let [^=]+)=(.*)$', r'\1:=\2 in', line)
    line = re.sub(r'\\([^ ->]+)\s*->', r'fun \1 =>', line)
    
    # in most cases, setRegister is the last statement and therefore does
    # not need ";;", but in the Jal and Jalr case, it's not the last one
    if casename == "Jal" or casename == "Jalr":
        line = re.sub(r'^(\s*setRegister.*)$', r'\1;;', line)

    line = line.replace('::', ':')
    line = line.replace('.&.', '<&>')
    line = line.replace('.|.', '<|>')
    line = line.replace('mod ', 'rem ')
    line = line.replace(' 4', ' four')
    line = line.replace(' 2', ' two')
    line = line.replace(' 1', ' one')
    line = line.replace(' 0', ' zero')

    if re.match(r'.*unsigned.*', line):
        line = line.replace(' < ', ' <u ')
        line = line.replace(' >= ', ' >=u ')

    m = re.match(r'execute\s*\((([^ ]+)[^)]+)\)\s*=\s*(\w+)(.*)', line)
    if m:
        pattern = m.group(1)
        newcasename = m.group(2)
        firstword = m.group(3)
        rest = m.group(4)
        if firstword == "do":
            if re.match(blacklist, casename):
                prefix = "*)| "
            else:
                prefix = "  | " 
            casename = newcasename
            if re.match(blacklist, casename):
                suffix = " => Return tt (*"
            else:
                suffix = " =>"
            line = prefix + pattern + suffix
        else:
            line = "  | " + pattern + " =>\n      " + extra_indent + firstword + rest
    else:
        line = "    " + line

    line = re.sub(r'do\s*$', '', line)

    return extra_indent + line


def convert(hs_filepath, coq_filepath):
    prefix, suffix = read_coq_template(coq_filepath)
    with open(hs_filepath) as f, open(coq_filepath, 'w') as g:
        g.write(prefix)
        is_inside = False
        for l in f:
            line = l.rstrip()
            if line == "-- begin ast":
                is_inside = True
            elif line == "-- end ast":
                is_inside = False
            elif is_inside:
                g.write(convert_line(line))
                g.write('\n')
        g.write(suffix)


convert('../../riscv-semantics/src/ExecuteI.hs', '../src/Execute.v')


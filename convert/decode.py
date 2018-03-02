import re

def skip_until(f, regex):
    while True:
        line = f.readline()
        assert line, "Ran past eof without encountering any line matching '{}'".format(regex)
        if re.match(regex, line.rstrip()):
            break


def read_until(f, regex):
    res = ''
    while True:
        line = f.readline()
        assert line, "Ran past eof without encountering any line matching '{}'".format(regex)
        if re.match(regex, line.rstrip()):
            break
        else:
            res += line
    return res


def read_until_eof(f):
    res = ''
    while True:
        line = f.readline()
        if not line:
            break
        else:
            res += line
    return res


def skip_while(f, regex):
    while True:
        line = f.readline().rstrip()
        if not re.match(regex, line):
            break


def skip_n(f, n, regex):
    for _ in range(n):
        line = f.readline().rstrip()
        assert re.match(regex, line), "line '{}' does not match regex '{}'".format(line, regex)


def skip_one(f, regex):
    skip_n(f, 1, regex)


def read_coq_template(coq_filepath):
    markers = ['instructions', 'constants', 'decode']
    with open(coq_filepath) as f:
        res = []
        for keyword in markers:
            res.append(read_until(f, r'\s*\(\* begin ' + keyword + r' \*\)'))
            skip_until(f, r'\s*\(\* end ' + keyword + r' \*\)')
        res.append(read_until_eof(f))
    for i, keyword in enumerate(markers):
        res[i] = res[i] + '(* begin ' + keyword + ' *)\n'
        res[i+1] = '(* end ' + keyword + ' *)\n' + res[i+1]
    return res


def test_read_coq_template():
    print 'HOLE\n'.join(read_coq_template('../src/Decode.v'))


def convert(hs_filepath, coq_filepath):
    template = read_coq_template(coq_filepath)
    with open(hs_filepath) as f, open(coq_filepath, 'w') as g:
        g.write(template[0])
        
        # instructions
        skip_until(f, 'data Instruction =')
        while True:
            line = f.readline()
            assert line, "eof before finishing reading instructions"
            line = line.rstrip()
            if line != "":
                if re.match(r'\s*deriving \(Eq, Read, Show\)', line):
                    break
                m = re.match(r'\s*([^ {]+)\s*(({[^}]+})?)\s*\|?\s*', line)
                assert m, 'unexpected line: ' + line
                casename = m.group(1)
                args = m.group(2)
                args = re.sub(r'{\s*', '(', args)
                args = re.sub(r'\s*}', ')', args)
                args = re.sub(r'\s*::', ':', args)
                args = re.sub(r',\s*', ')(', args)
                line = '  | ' + casename + args
            g.write(line)
            g.write('\n')
        
        g.write(template[1])
        
        # constants
        skip_until(f, 'type Opcode = MachineInt')
        while True:
            line = f.readline()
            assert line, "eof before finishing reading constants"
            line = line.rstrip()
            if re.match('-- =+', line):
                break
            m = re.match(r'^\s*--(.*)$', line)
            if m:
                line = '(*' + m.group(1) + ' *)'
            elif line != "":
                m = re.match(r'([^ :]+\s*)::.*--\s*\d+.b([01_]+)\s*', line)
                assert m, "line '{}' didn't match constant pattern".format(line)
                constname = m.group(1)
                binstr = m.group(2)
                binstr = binstr.replace('_', '')
                line = 'Definition ' + constname + ' := Ob"' + binstr + '".'
            g.write(line)
            g.write('\n')
        
        g.write(template[2])
        
        # decode
        skip_until(f, r'decode\s*:: Int -> MachineInt -> Instruction')
        skip_one(f, r'decode.*=\s*decode_sub.*')
        skip_one(f, r'\s*where\s*')
        # let bindings extracting bit patterns from instruction:
        parensToClose = 0
        while True:
            line = f.readline().rstrip()
            if re.match(r'\s*decode_sub.*', line):
                break
            elif re.match(r'^\s*--.*$', line):
                continue
            line = line.split("--")[0].rstrip()
            line = re.sub(r'^(\s*)([^=]+)=', r'\1let \2:=', line)
            m = re.match(r'^(.*)\$\s*(.*)$', line)
            if m:
                parensToClose += 1
                line = m.group(1) + '(' + m.group(2)
            if re.match(r'^.*(\)|\d)$', line):
                line = line + ''.join([')' for _ in range(parensToClose)]) + " in"
                parensToClose = 0
            line = line.replace('.|.', '<|>')
            g.write(line)
            g.write('\n')
        # big if
        while True:
            line = f.readline().rstrip()
            if re.match(r'\s*\|\s*True\s*=\s*InvalidInstruction', line):
                break
            elif re.match(r'^\s*--.*$', line):
                continue
            line = line.split("--")[0].rstrip()
            if line != "":
                m = re.match(r'\s*\|((?:\s*[^= ,]+\s*==\s*[^= ,]+\s*,?\s*)+)=\s*([^= ,]+)\s*(.*)', line)
                assert m, "line '{}' did not match regex".format(line)
                cond = m.group(1).strip()
                casename = m.group(2)
                args = m.group(3)
                cond = cond.replace('==', ' =? ')
                cond = re.sub(r'\s*,\s*', ') && (', cond)
                args = re.sub('[^ =,]+\s*=\s*([^ =,]+)', r'\1', args)
                args = args.replace('{', '').replace('}', '').replace(',', '')
                line = '    if (' + cond + ') then ' + casename + ' ' + args + ' else'
            g.write(line)
            g.write('\n')
        
        g.write(template[3])

convert('../../riscv-semantics/src/Decode.hs', '../src/Decode.v')



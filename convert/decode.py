import re

def skip_until(f, regex):
    while True:
        line = f.readline().rstrip()
        if re.match(regex, line):
            break


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


def convert(hs_filepath, coq_filepath):
    with open(hs_filepath) as f, open(coq_filepath, 'w') as g:
        skip_until(f, r'decode\s*:: Int -> MachineInt -> Instruction')
        skip_one(f, r'decode.*=\s*decode_sub.*')
        skip_one(f, r'\s*where\s*')
        while True:
            line = f.readline().rstrip()
            if re.match(r'\s*decode_sub.*', line):
                break
            elif re.match(r'\s*--.*', line):
                continue
            line = line.split("--")[0].rstrip()
            line = re.sub(r'^(\s*)([^=]+)=', r'\1let \2:=', line)
            if re.match(r'^.*(\)|\d)$', line):
                line = line + " in"
            line = line.replace('.|.', '<|>')

            g.write(line)
            g.write('\n')


convert('../../riscv-semantics/src/Decode.hs', '/tmp/decode_test.out')


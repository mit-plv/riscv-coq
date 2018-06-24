import json
from LanguagePrinter import LanguagePrinter

def getName(j):
    name = j['name']
    if name.startswith('coq_') or name.startswith('Coq_'):
        name = name[4:]
    return name.replace('.coq_', '.').replace('.Coq_', '.')


def type_glob_to_str(j):
    assert j['what'] == 'type:glob'
    assert j['args'] == []
    return getName(j)

    
def translate_type_decl(j, p):
    assert j['what'] == 'decl:type'
    name = getName(j)
    assert j['argnames'] == [], 'type aliases with parameters not supported'
    rhsName = type_glob_to_str(j['value'])
    p.type_alias(name, rhsName)


def is_enum(j):
    assert j['what'] == 'decl:ind'
    if len(j['argnames']) > 0:
        return False
    for constructor in j['constructors']:
        if len(constructor['argtypes']) > 0:
            return False
    return True


def translate_ind_decl(j, p):
    assert j['what'] == 'decl:ind'
    name = getName(j)
    if is_enum(j):
        constructorNames = [c['name'] for c in j['constructors']]
        p.enum(name, constructorNames)
    else:
        branches = [(
            b['name'],
            [type_glob_to_str(t) for t in b['argtypes']]
        ) for b in j['constructors']]
        p.variant(name, branches)


def get_signature(j, acc=[]):
    '''returns a tuple of (argTypesList, retType)'''
    if j['what'] == "type:arrow":
        t = type_glob_to_str(j['left']) # higher-order functions are not supported
        return get_signature(j['right'], [t] + acc)
    elif j['what'] == "type:glob":
        t = type_glob_to_str(j)
        return (acc, t)
    else:
        raise ValueError("unexpected 'what':" + j['what'])


def positive_to_bitstring(j):
    assert j['what'] == 'expr:constructor'
    constr = getName(j)
    if constr == 'BinNums.xH':
        return '1'
    elif constr == 'BinNums.xO':
        return positive_to_bitstring(j['args'][0]) + '0'
    elif constr == 'BinNums.xI':
        return positive_to_bitstring(j['args'][0]) + '1'
    else:
        raise ValueError('unexpected ' + constr)


def translate_expr(j, p):
    [s1, s2] = j['what'].split(':')
    assert s1 == 'expr'
    if s2 == 'constructor':
        if j['name'] == 'BinNums.Zpos':
            p.bit_literal(positive_to_bitstring(j['args'][0]))
        elif j['name'] == 'BinNums.Z0':
            p.bit_literal('0')
        else:
            print('TODO: ' + j['name'])
    elif s2 == 'lambda':
        ValueError('lambdas arbitrarily nested inside expressions are not supported')
    else:
        ValueError('unsupported ' + j['what'])


def strip_0arg_lambdas(j):
    if j['what'] == 'expr:lambda' and j['argnames'] == []:
        return strip_0arg_lambdas(j['body'])
    else:
        return j



# for debug printing
def ellipsis(j, fieldName):
    if isinstance(j, dict):
        if fieldName in j:
            if len(str(j[fieldName])) > 20:
                j[fieldName] = '...'
        for key in j:
            ellipsis(j[key], fieldName)
    elif isinstance(j, list):
        for child in j:
            ellipsis(child, fieldName)
    else:
        pass # primitive value, nothing to be done


didPrint = False

def translate_term_decl(j, p):
    global didPrint
    assert j['what'] == 'decl:term'
    sig = get_signature(j['type'])
    name = getName(j)
    if len(sig[0]) == 0:
        typ = sig[1]
        p.begin_constant_decl(name, typ)
        translate_expr(strip_0arg_lambdas(j['value']), p)
        p.end_constant_decl()
    else:
        if not didPrint:
            ellipsis(j, 'args')
            print(json.dumps(j, indent=3))
            didPrint = True



handlers = {
    'decl:type': translate_type_decl,
    'decl:ind' : translate_ind_decl,
    'decl:term': translate_term_decl
}


def translate(j, p):
    assert j['what'] == 'module'
    for decl in j['declarations']:
        name = getName(decl)
        if name.endswith('_rect') or name.endswith('_rec'):
            continue

        handler = handlers.get(decl['what'])
        if handler:
            handler(decl, p)
        else:
            print('Error: no handler for {}'.format(decl['what']))
            print(json.dumps(decl, indent=3))
            break

        # p.writeln(name)
    # p.writeln('\n'.join([d['name'] for d in j['declarations']]))
    # p.writeln(str(j.keys()))
    

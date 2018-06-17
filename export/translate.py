import json
from LanguagePrinter import LanguagePrinter

def getName(j):
    name = j['name']
    if name.startswith('coq_'):
        name = name[4:]
    return name


def type_glob_to_str(j):
    assert j['what'] == 'type:glob'
    assert j['args'] == []
    return j['name']

    
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
    if is_enum(j):
        name = getName(j)
        constructorNames = [c['name'] for c in j['constructors']]
        p.enum(name, constructorNames)
    else:
        print('not an enum:')
        print(json.dumps(j, indent=3))


handlers = {
    'decl:type': translate_type_decl,
    'decl:ind':  translate_ind_decl
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
    

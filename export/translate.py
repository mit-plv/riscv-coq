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
    global constructor2Type, enumval2Type
    assert j['what'] == 'decl:ind'
    name = getName(j)
    if is_enum(j):
        constructorNames = [getName(c) for c in j['constructors']]
        p.enum(name, constructorNames)
        for c in j['constructors']:
            enumval2Type[getName(c)] = name
    else:
        branches = [(
            getName(b),
            [type_glob_to_str(t) for t in b['argtypes']]
        ) for b in j['constructors']]
        p.variant(name, branches)
        for c in j['constructors']:
            constructor2Type[getName(c)] = name


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


def get_lambda_argnames(j):
    '''returns a list of argument names'''
    assert j['what'] == "expr:lambda"
    return j['argnames']


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

# maps constructor names to type names
constructor2Type = {}

# maps enum values to name of the enum
enumval2Type = {}


def translate_match(j, p):
    '''case distinction over a variant (inductive)'''
    global constructor2Type
    assert j['what'] == 'expr:case'
    assert j['expr']['what'] == 'expr:rel', "match can only discriminate on var, not any expr"
    discriminee = getName(j['expr'])
    p.begin_match(discriminee)
    for c in j['cases']:
        assert c['what'] == 'case'
        if c['pat']['what'] == 'pat:constructor':
            constructorName = getName(c['pat'])
            argNames = c['pat']['argnames']
            p.begin_match_case(discriminee, constructorName, argNames)
            translate_expr(c['body'], p, "Return")
            p.end_match_case()
        elif c['pat']['what'] == 'pat:wild':
            p.begin_match_default_case()
            translate_expr(c['body'], p, "Return")
            p.end_match_default_case()
        else:
            raise ValueError("unknown " + c['pat']['what'])
    p.end_match()


def translate_switch(j, p):
    '''case distinction over an enum'''
    global enumval2Type
    assert j['what'] == 'expr:case'
    assert j['expr']['what'] == 'expr:rel', "switch can only discriminate on var, not any expr"
    discriminee = getName(j['expr'])
    p.begin_switch(discriminee)
    for c in j['cases']:
        assert c['what'] == 'case'
        if c['pat']['what'] == 'pat:constructor':
            constructorName = getName(c['pat'])
            p.begin_switch_case(discriminee, constructorName, enumval2Type[constructorName])
            translate_expr(c['body'], p, "Return")
            p.end_switch_case()
        elif c['pat']['what'] == 'pat:wild':
            p.begin_switch_default_case()
            translate_expr(c['body'], p, "Return")
            p.end_switch_default_case()
        else:
            raise ValueError("unknown " + c['pat']['what'])
    p.end_switch()

def lazy_translate_expr(j, p, doReturn):
    return (lambda: translate_expr(j, p, doReturn))

def translate_expr(j, p, doReturn):
    """ doReturn maybe be CondExpr, Return or NoReturn """
    global constructor2Type, enumval2Type, didPrint
    try:
        [s1, s2] = j['what'].split(':')
    except:
        print(j)
    assert s1 == 'expr'
    if s2 == 'constructor':
        if doReturn == "Return": p.begin_return_expr()
        constructorName = getName(j)
        if constructorName == 'BinNums.Zpos':
            p.bit_literal(positive_to_bitstring(j['args'][0]))
        elif constructorName == 'BinNums.Z0':
            p.bit_literal('0')
        elif constructorName == 'Datatypes.nil':
            p.list([])
        elif constructorName == 'Datatypes.O':
            p.bit_literal('0')
        elif constructorName == 'Datatypes.cons':
            if getName(j['args'][1]) != "Datatypes.nil":
               raise ValueError("cons is only supported to create singleton list")
            p.list([lambda: translate_expr(j['args'][0],p,"CondExpr")])
        elif constructorName == 'Datatypes.true':
            p.true_literal()
        elif constructorName == 'Datatypes.false':
            p.false_literal()
        elif "." not in constructorName: # Constructor is an app, right?
            name = j["name"]
            j["func"] = {
                "name": name,
                "what" : "expr:global"
                }
            del j["name"]
            j["what"] = "expr:apply"
            translate_expr(j,p, "CondExpr")
        else:
            print('TODO: ' + j['name'])
        if doReturn == "Return": p.end_return_expr()
    elif s2 == 'let':
        if j['nameval']['what']=="expr:let":
            raise ValueError(" let a = let b is not legal in the input")
        # TODO we need to get the right type for C here instead of None
        p.local_var_decl(j['name'], None, lambda: translate_expr(j['nameval'], p, "CondExpr"))
        translate_expr(j['body'], p, doReturn)
    elif s2 == 'apply':
        # if not didPrint:
        #     ellipsisN(j, 3)
        #     print(json.dumps(j, indent=4))
        #     didPrint = True
        #     raise ValueError('What does an apply looks like')
        if doReturn == "Return": p.begin_return_expr()
        functionName = getName(j['func'])
        if functionName == 'Datatypes.app':
            # translate_expr + translate_expr
            p.concat((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                     (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'Datatypes.andb':
            p.boolean_and((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                          (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'Datatypes.orb':
            p.boolean_or((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                         (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'Datatypes.length':
            p.list_length((lambda: translate_expr(j['args'][0],p,"CondExpr")))
        elif functionName == 'List.nth':
            p.list_nth_default((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                               (lambda: translate_expr(j['args'][1],p,"CondExpr")),
                               (lambda: translate_expr(j['args'][2],p,"CondExpr")))
        elif functionName == 'BinInt.Z.lor':
            p.logical_or((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                       (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'BinInt.Z.shiftl':
            p.shift_left((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                       (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'BinInt.Z.eqb':
            p.equality((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                       (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'BinInt.Z.gtb':
            p.gt((lambda: translate_expr(j['args'][0],p,"CondExpr")),
                 (lambda: translate_expr(j['args'][1],p,"CondExpr")))
        elif functionName == 'BinInt.Z.of_nat' or functionName == "Utility.machineIntToShamt" :
            translate_expr(j['args'][0],p,"CondExpr")
        else:
            p.function_call(
                lambda: translate_expr(j['func'], p, "CondExpr"),
                [lazy_translate_expr(arg, p, "CondExpr") for arg in j['args']])
    elif s2 == 'global':
        p.var(j['name'])
    elif s2 == 'lambda':
        ValueError('lambdas arbitrarily nested inside expressions are not supported')
    elif s2 == 'case':
        if doReturn == "NoReturn":
            p.flush()
            if not didPrint:
                ellipsisN(j, 3)
                print(json.dumps(j, indent=4))
                didPrint = True

            raise ValueError('match is only supported if the branches are allowed to return')
        firstConstructorName = getName(j['cases'][0]['pat'])
        if firstConstructorName in constructor2Type:
            translate_match(j, p)
        elif firstConstructorName in enumval2Type:
            translate_switch(j, p)
        elif doReturn == "CondExpr" and firstConstructorName == "Datatypes.true" : # Assuming that the first case is the if true
            p.if_expr((lambda: translate_expr(j["expr"], p, "NoReturn")),
                      (lambda: translate_expr(j["cases"][0]["body"], p, "CondExpr")),
                      (lambda: translate_expr(j["cases"][1]["body"], p, "CondExpr")))
        elif firstConstructorName == "Datatypes.true":
            p.if_stmt((lambda: translate_expr(j["expr"], p, "NoReturn")),
                      (lambda: translate_expr(j["cases"][0]["body"], p, doReturn)),
                      (lambda: translate_expr(j["cases"][1]["body"], p, doReturn)))

            # p.flush()
            # if not didPrint:
            #     ellipsisN(j, 4)
            #     print(json.dumps(j, indent=4))
            #     didPrint = True
            # raise ValueError('Just arrived here')
        else:
            p.flush()
            if not didPrint:
                ellipsisN(j, 4)
                print(json.dumps(j, indent=4))
                didPrint = True
            raise ValueError('unknown ' + firstConstructorName)
    elif s2 == 'rel':
        if doReturn == "Return": p.begin_return_expr()
        p.var(getName(j))
        if doReturn == "Return": p.end_return_expr()
    else:
        p.comment('TODO ' + j['what'])
        p.nop()
        if not didPrint:
            ellipsisN(j, 3)
            print(json.dumps(j, indent=3))
            didPrint = True

        # ValueError('unsupported ' + j['what'])


def strip_0arg_lambdas(j):
    if j['what'] == 'expr:lambda' and j['argnames'] == []:
        return strip_0arg_lambdas(j['body'])
    else:
        return j

def ellipsisN(j, n):
    if n==0:
        if isinstance(j, dict) or isinstance(j, list):
            j.clear()
    else:
        if isinstance(j, dict):
            for key in j:
                ellipsisN(j[key], n-1)
        elif isinstance(j, list):
            for child in j:
                ellipsisN(child, n-1)
        else:
            pass # primitive value, nothing to be done


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
    # if name == "supportsA":
    #     if not didPrint:
    #         ellipsis(j, 'args')
    #         print(json.dumps(j, indent=3))
    #         didPrint = True
    #         raise ValueError("Sad")

    if len(sig[0]) == 0:
        typ = sig[1]
        p.constant_decl(name, typ,
                        lambda: translate_expr(strip_0arg_lambdas(j['value']), p, "NoReturn"))
    else:
        argnames = get_lambda_argnames(j['value'])
        if len(argnames) != len(sig[0]):
            raise ValueError(
                "number of args in type signature doesn't match number of args " +
                "in lambda, probably because the function body returns a function, " +
                "but higer order functions are not supported")
        argnamesWithTypes = zip(argnames, sig[0])
        returnType = sig[1]
        p.begin_fun_decl(name, argnamesWithTypes, returnType)
        translate_expr(j['value']['body'], p, "Return")
        p.end_fun_decl()



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

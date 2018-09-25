import json
from LanguagePrinter import LanguagePrinter

def getName(j):
    name = j['name']
    if name.startswith('coq_') or name.startswith('Coq_'):
        name = name[4:]
    return name.replace('.coq_', '.').replace('.Coq_', '.')


def type_glob_to_str(j, ignoreFailures=False):
    if not ignoreFailures:
        assert j['what'] == 'type:glob'
        if j['args'] != []:
            ellipsisN(j, 3)
            print(json.dumps(j, indent=4))
            raise ValueError('polymorphic types are not supported')
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


def get_signature(j, acc=[], ignoreFailures=False):
    '''returns a tuple of (argTypesList, retType)'''
    if j['what'] == "type:arrow":
        t = type_glob_to_str(j['left'], ignoreFailures)
        return get_signature(j['right'], acc + [t], ignoreFailures)
    elif j['what'] == "type:glob":
        t = type_glob_to_str(j, ignoreFailures)
        return (acc, t)
    else:
        if ignoreFailures:
            return (acc, None)
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
    assert j['what'] == 'expr:case'
    assert j['expr']['what'] == 'expr:rel', "match can only discriminate on var, not any expr"
    discriminee = getName(j['expr'])
    branches = {}
    default_branch = None
    for c in j['cases']:
        assert c['what'] == 'case'
        if c['pat']['what'] == 'pat:constructor':
            constructorName = getName(c['pat'])
            argNames = c['pat']['argnames']
            branches[constructorName] = (argNames, lazy_translate_expr(c['body'], p, 'toStmt'))
        elif c['pat']['what'] == 'pat:wild':
            default_branch = lazy_translate_expr(c['body'], p, 'toStmt')
        else:
            raise ValueError("unknown " + c['pat']['what'])
    return p.stmt.match(discriminee, branches, default_branch)


def translate_switch(j, p):
    '''case distinction over an enum'''
    global enumval2Type
    assert j['what'] == 'expr:case'
    assert j['expr']['what'] == 'expr:rel', "switch can only discriminate on var, not any expr"
    discriminee = getName(j['expr'])
    enumName = 'Whoops_unknown_enum_name'
    branches = {}
    default_branch = None
    for c in j['cases']:
        assert c['what'] == 'case'
        if c['pat']['what'] == 'pat:constructor':
            constructorName = getName(c['pat'])
            enumName = enumval2Type[constructorName]
            branches[constructorName] = lazy_translate_expr(c['body'], p, 'toStmt')
        elif c['pat']['what'] == 'pat:wild':
            default_branch = lazy_translate_expr(c['body'], p, 'toStmt')
        else:
            raise ValueError("unknown " + c['pat']['what'])
    return p.stmt.switch(discriminee, enumName, branches, default_branch)


funcs_with_ignored_arg0 = [
    'Utility.add',
    'Utility.sub',
    'Utility.mul',
    'Utility.div',
    'Utility.rem',
    'Utility.negate',
    'Utility.reg_eqb',
    'Utility.signed_less_than',
    'Utility.ltu',
    'Utility.xor',
    'Utility.or',
    'Utility.and',
    'Utility.regToInt8'  ,
    'Utility.regToInt16' ,
    'Utility.regToInt32' ,
    'Utility.regToInt64' ,
    'Utility.uInt8ToReg' ,
    'Utility.uInt16ToReg',
    'Utility.uInt32ToReg',
    'Utility.uInt64ToReg',
    'Utility.int8ToReg'  ,
    'Utility.int16ToReg' ,
    'Utility.int32ToReg' ,
    'Utility.int64ToReg' ,
    'Utility.s32',
    'Utility.u32',
    'Utility.regToZ_signed',
    'Utility.regToZ_unsigned',
    'Utility.sll',
    'Utility.srl',
    'Utility.sra',
    'Utility.divu',
    'Utility.remu',
    'Utility.maxSigned',
    'Utility.maxUnsigned',
    'Utility.minSigned',
    'Utility.regToShamt5',
    'Utility.regToShamt',
    'Utility.highBits',
    'Utility.ZToReg',

    # derived functions:
    'Utility.lnot'
]


stringly_typed = {
    # Decode:
    'aqrl': 'BinNums.Z',
    'funct5': 'BinNums.Z',
    'zimm': 'BinNums.Z',
    'funct6': 'BinNums.Z',
    'shamtHi': 'BinNums.Z',
    'shamtHiTest': 'Datatypes.bool',
    'shamt6': 'BinNums.Z',
    'shamt5': 'BinNums.Z',
    'sbimm12': 'BinNums.Z',
    'simm12': 'BinNums.Z',
    'csr12': 'BinNums.Z',
    'oimm12': 'BinNums.Z',
    'imm12': 'BinNums.Z',
    'jimm20': 'BinNums.Z',
    'oimm20': 'BinNums.Z',
    'imm20': 'BinNums.Z',
    'msb4': 'BinNums.Z',
    'pred': 'BinNums.Z',
    'succ': 'BinNums.Z',
    'rs2': 'BinNums.Z',
    'rs1': 'BinNums.Z',
    'rd': 'BinNums.Z',
    'funct12': 'BinNums.Z',
    'funct7': 'BinNums.Z',
    'funct3': 'BinNums.Z',
    'opcode': 'BinNums.Z',
    'decodeI': 'InstructionI',
    'decodeM': 'InstructionM',
    'decodeA': 'InstructionA',
    'decodeI64': 'InstructionI64',
    'decodeM64': 'InstructionM64',
    'decodeA64': 'InstructionA64',
    'decodeCSR': 'InstructionCSR',
    'resultCSR': 'InstructionList',
    'resultA64': 'InstructionList',
    'resultM64': 'InstructionList',
    'resultI64': 'InstructionList',
    'resultA': 'InstructionList',
    'resultM': 'InstructionList',
    'resultI': 'InstructionList',
    'results': 'InstructionList',

    # Execute:
    'a': 't',
    'addr': 't',
    'val': 't',
    'pc': 't',
    'newPC': 't',
    'x': 't',
    'y': 't',
    'q': 't',
    'r': 't',
    '_': 'unit'
}

def varname_to_type(name):
    global stringly_typed
    if name in stringly_typed:
        return stringly_typed[name]
    else:
        print("Don't know the type of " + name)
        stringly_typed[name] = 'void'
        return 'void'

def lazy_translate_expr(j, p, mode):
    return (lambda: translate_expr(j, p, mode))


def augment_dict_with_alternative_names(d):
    res = {}
    for k in d:
        res[k] = d[k]
        res[k.replace('BinInt.Z', 'BinIntDef.Z')] = d[k]
    return res


def translate_expr(j, p, mode):
    """
    mode can be 'toExpr' (prints as an expression)
             or 'toStmt' (prints as a statement ending in a return)
    """
    global constructor2Type, enumval2Type, didPrint
    try:
        [s1, s2] = j['what'].split(':')
    except:
        print(j)
    assert s1 == 'expr'

    def maybe_return(res):
        if mode == 'toExpr':
            return res
        elif mode == 'toStmt':
            return p.stmt.return_value(res)
        else:
            raise ValueError("unknown mode: " + mode)

    if s2 == 'constructor':
        constructorName = getName(j)
        if constructorName == 'BinNums.Zpos':
            res = p.expr.bit_literal(positive_to_bitstring(j['args'][0]))
        elif constructorName == 'BinNums.Z0':
            res = p.expr.bit_literal('0')
        elif constructorName == 'Datatypes.nil':
            res = p.expr.list([])
        elif constructorName == 'Datatypes.O':
            res = p.expr.bit_literal('0')
        elif constructorName == 'Datatypes.cons':
            if getName(j['args'][1]) != "Datatypes.nil":
               raise ValueError("cons is only supported to create singleton list")
            res = p.expr.list([lazy_translate_expr(j['args'][0], p, 'toExpr')])
        elif constructorName == 'Datatypes.true':
            res = p.expr.true_literal()
        elif constructorName == 'Datatypes.false':
            res = p.expr.false_literal()
        elif constructorName == 'Program.Load':
            res = p.expr.access_type_load()
        elif constructorName == 'Program.Store':
            res = p.expr.access_type_store()
        elif "." not in constructorName: # Constructor is an app, right?
            name = j["name"]
            j["func"] = {
                "name": name,
                "what" : "expr:global"
                }
            del j["name"]
            j["what"] = "expr:apply"
            res = translate_expr(j, p, 'toExpr')
        else:
            print('TODO: ' + j['name'])
            res = 'TODO({})'.format(j['name']) # default value
        return maybe_return(res)

    elif s2 == 'let':
        if mode != 'toStmt':
            raise ValueError("a let expression cannot be translated to " +
                             "an expression, but only to a statement")
        # TODO we need to get the right type for C here instead of just assuming int32_t
        return p.stmt.let_in(j['name'], varname_to_type(j['name']),
                             lazy_translate_expr(j['nameval'], p, 'toExpr'),
                             lazy_translate_expr(j['body'], p, 'toStmt'))

    elif s2 == 'apply':
        # if not didPrint:
        #     ellipsisN(j, 3)
        #     print(json.dumps(j, indent=4))
        #     didPrint = True
        #     raise ValueError('What does an apply looks like')
        functionName = getName(j['func'])

        if functionName == 'Monads.Bind':
            # j['args'][0] is the monad instance (ignored)
            rhs = j['args'][1] # first arg of Bind, i.e. rhs of assignment being made
            f = j['args'][2]   # second arg of Bind, i.e. a lambda
            if f['what'] != 'expr:lambda':
                raise ValueError('Bind only accepts inlined lambdas as function argument')
            binder = f['argnames'][0]
            return p.stmt.let_in(binder, varname_to_type(binder),
                                 lazy_translate_expr(rhs, p, 'toExpr'),
                                 lazy_translate_expr(f['body'], p, 'toStmt'))

        if functionName == 'Monads.Return':
            # j['args'][0] is the monad instance (ignored)
            assert getName(j['args'][1]) == 'Datatypes.tt' # can only return unit
            return None # to get empty else-branch

        # see RiscvProgram and RiscvState in Program.v
        # maps opname to numOfIgnoredArgs
        riscv_monad_ops = {
            # RiscvProgram
            'Program.getRegister': 3,
            'Program.setRegister': 3,
            'Program.loadByte': 3,
            'Program.loadHalf': 3,
            'Program.loadWord': 3,
            'Program.loadDouble': 3,
            'Program.storeByte': 3,
            'Program.storeHalf': 3,
            'Program.storeWord': 3,
            'Program.storeDouble': 3,
            'Program.getPC': 3,
            'Program.setPC': 3,
            'Program.getCSRField_MTVecBase': 3,
            'Program.step': 3,
            'Program.endCycle': 3,
            # RiscvState
            'Program.raiseException': 4,
            'Program.translate': 4
        }

        if functionName in riscv_monad_ops:
            numberOfIgnoredArgs = riscv_monad_ops[functionName]
            stateArg = {
                "what": "expr:rel",
                "name": "s"
            }
            j['args'] = [stateArg] + j['args'][numberOfIgnoredArgs:]
            res = p.expr.function_call(
                lazy_translate_expr(j['func'], p, 'toExpr'),
                [lazy_translate_expr(arg, p, 'toExpr') for arg in j['args']])
            if mode == 'toExpr':
                return res
            elif mode == 'toStmt':
                # last statement in execute returns void, no need for return,
                # but we do need a semicolon
                return res + ';'
            else:
                raise ValueError("unknown mode: " + mode)

        unary_funcs = augment_dict_with_alternative_names({
            'Datatypes.negb': p.expr.negate_bool,
            'Datatypes.length': p.expr.list_length,
            'BinInt.Z.of_nat': p.expr.silent_id,
            'Utility.machineIntToShamt': p.expr.silent_id
        })
        binary_funcs = augment_dict_with_alternative_names({
            'Datatypes.app': p.expr.concat,
            'Datatypes.andb': p.expr.boolean_and,
            'Datatypes.orb': p.expr.boolean_or,
            'BinInt.Z.lor': p.expr.logical_or,
            'BinInt.Z.shiftl': p.expr.shift_left,
            'BinInt.Z.mul': p.expr.bigint_mul,
            'BinInt.Z.eqb': p.expr.equality,
            'BinInt.Z.gtb': p.expr.gt
        })
        ternary_funcs = augment_dict_with_alternative_names({
            'List.nth': p.expr.list_nth_default
        })

        if functionName in unary_funcs:
            res = unary_funcs[functionName](lazy_translate_expr(j['args'][0], p, 'toExpr'))
        elif functionName in binary_funcs:
            res = binary_funcs[functionName](lazy_translate_expr(j['args'][0], p, 'toExpr'),
                                             lazy_translate_expr(j['args'][1], p, 'toExpr'))
        elif functionName in ternary_funcs:
            res = ternary_funcs[functionName](lazy_translate_expr(j['args'][0], p, 'toExpr'),
                                             lazy_translate_expr(j['args'][1], p, 'toExpr'),
                                             lazy_translate_expr(j['args'][2], p, 'toExpr'))
        else:
            if functionName in funcs_with_ignored_arg0:
                j['args'] = j['args'][1:]
                j['func']['name'] = p.expr.alu_op_name(
                    strip_prefix('Utility.', getName(j['func'])))
            res = p.expr.function_call(
                lazy_translate_expr(j['func'], p, 'toExpr'),
                [lazy_translate_expr(arg, p, 'toExpr') for arg in j['args']])
        return maybe_return(res)

    elif s2 == 'global':
        return maybe_return(p.expr.var(getName(j)))

    elif s2 == 'lambda':
        ellipsisN(j, 4)
        print(json.dumps(j, indent=4))
        raise ValueError('lambdas arbitrarily nested inside expressions are not supported')

    elif s2 == 'case':
        firstConstructorName = getName(j['cases'][0]['pat'])
        if firstConstructorName == "Datatypes.true":
            if mode == 'toExpr':
                return p.expr.if_expr(
                    lazy_translate_expr(j["expr"], p, 'toExpr'),
                    lazy_translate_expr(j["cases"][0]["body"], p, 'toExpr'),
                    lazy_translate_expr(j["cases"][1]["body"], p, 'toExpr'))
            elif mode == 'toStmt':
                return p.stmt.if_stmt(
                    lazy_translate_expr(j["expr"], p, 'toExpr'),
                    lazy_translate_expr(j["cases"][0]["body"], p, 'toStmt'),
                    lazy_translate_expr(j["cases"][1]["body"], p, 'toStmt'))
            else:
                raise ValueError("unknown mode: " + mode)
        else:
            if mode != 'toStmt':
                ellipsisN(j, 3)
                print(json.dumps(j, indent=4))
                raise ValueError('match is only supported if the branches are allowed to return')
            if firstConstructorName in constructor2Type:
                return translate_match(j, p)
            elif firstConstructorName in enumval2Type:
                return translate_switch(j, p)
            else:
                ellipsisN(j, 4)
                print(json.dumps(j, indent=4))
                raise ValueError('unknown ' + firstConstructorName)

    elif s2 == 'rel':
        return maybe_return(p.expr.var(getName(j)))

    else:
        # ValueError('unsupported ' + j['what'])
        return maybe_return('TODO({})'.format(j['what']))


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


def strip_prefix(prefix, s):
    assert s.startswith(prefix)
    return s[len(prefix):len(s)]


didPrint = False

def translate_term_decl(j, p):
    global didPrint
    assert j['what'] == 'decl:term'
    name = getName(j)
    if name == 'execute':
        sig = get_signature(j['type'], ignoreFailures=True)
        extension = strip_prefix('Decode.Instruction', sig[0][-1])
        print(extension)
        # j = j['value']['body']['cases']
        # ellipsisN(j, 3)
        # print(json.dumps(j, indent=3))
        translate_execute(j['value']['body']['cases'], p, extension)
    else:
        sig = get_signature(j['type'])
        if len(sig[0]) == 0:
            typ = sig[1]
            p.constant_decl(name, typ,
                            lazy_translate_expr(strip_0arg_lambdas(j['value']), p, 'toExpr'))
        else:
            argnames = get_lambda_argnames(j['value'])
            if len(argnames) != len(sig[0]):
                raise ValueError(
                    "number of args in type signature doesn't match number of args " +
                    "in lambda, probably because the function body returns a function, " +
                    "but higer order functions are not supported")
            argnamesWithTypes = zip(argnames, sig[0])
            returnType = sig[1]
            p.fun_decl(name, argnamesWithTypes, returnType,
                       lazy_translate_expr(j['value']['body'], p, 'toStmt'))


def translate_execute(js, p, extension):
    global didPrint
    p.begin_extension(extension)
    for j in js:
        assert j['what'] == 'case'
        if j['pat']['what'] == 'pat:wild':
            continue # first kind of default case
        assert j['pat']['what'] == 'pat:constructor'
        if j['pat']['name'] == 'Decode.Invalid' + extension:
            continue # second kind of default case
        p.execute_case(strip_prefix('Decode.', j['pat']['name']),
                       j['pat']['argnames'],
                       lazy_translate_expr(j['body'], p, 'toStmt'))
    p.end_extension()


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

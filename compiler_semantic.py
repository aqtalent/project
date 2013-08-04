import compiler_parser
import compiler_symbol_table

# definition of w(E, P, T)
class Proof_Term_Context(object):
    def __init__(self, e = None, p = None, t = None, org_context = None):
        if not isinstance(org_context,Proof_Term_Context):
            self.e = e
            self.p = p
            self.t = t
        else:
            self.e.table = self.update_context(org_context.e, e)
            self.p.table = self.update_context(org_context.p, p)
            self.t.table = self.update_context(org_context.t, t)

        self.change_time = 0 # run assignment statement a time, change_time + 1

    def update_context(self, org_context, new_context):
        result = {}
        for key in org_context.table:
            result[key] = org_context.table[key]
        for key in new_context.table:
            result[key] = new_context.table[key]
        return result

    def get_symbol(self, name, proof):
        #print name, 'hello', proof.symbol_table
        org_context = proof.symbol_table
        for table, scope in [(self.t.table, 't'), (org_context.t.table, 't'),
                             (self.p.table, 'p'), (org_context.p.table, 'p'),
                             (self.e.table, 'e'), (org_context.e.table, 'e')]:
            #print table, 'Hello'
            if table != None and table.has_key(name):
                if isinstance(table[name], compiler_symbol_table.Node):
                    if table[name].symbol_type == 'ID':
                        #print 'World Hello', table[name], table[name].value
                        #return table[name].value_type, table[name].value[1], scope
                        return table[name].value_type, table[name], scope
                    else:   # CONST
                        # print table[name].value
                        #print table[name].symbol_type, name, '123'
                        return table[name].value_type, table[name], scope
                else: # function
                    # Bug?
                    #print name, table[name]
                    return table[name].value_type, table[name], scope
        return None, None, None

class Proposition(object):
    def __init__(self, e = None, p = None, t = None, org_context = None,
                 symbol_table = None,
                 expression = None,
                 prop_type = None):
        # w(E, P, T)
        if e == None:
            e = compiler_symbol_table.Symbol_Table(table = {})
        if p == None:
            p = compiler_symbol_table.Symbol_Table(table = {})
        if t == None:
            t = compiler_symbol_table.Symbol_Table(table = {})
        self.context = Proof_Term_Context(e, p, t, org_context)

        # w(E, P, T) after running the statement
        #self.after_context = 

        # w(E, P, T) of the start of the function,
        # an instance of Proof_Term_Context
        self.symbol_table = symbol_table

        # expression
        self.expression = expression

        # Type of proposition: statement/math/proposition
        self.prop_type = prop_type

        # No. of statement list (Q1, Q2, ...)
        self.qid = 0

    def equal(self, other):
        pass

    def update_context(self, new_context):
        for key in new_context.e.table:
            self.context.e.table[key] = new_context.e.table[key]
        for key in new_context.p.table:
            #print key, new_context.p.table[key]
            self.context.p.table[key] = new_context.p.table[key]
        for key in new_context.t.table:
            self.context.t.table[key] = new_context.t.table[key]

class Proof_Term(object):
    def __init__(self, pid = 1, term = None, reason = None):
        # Ai = ...
        self.pid = pid
        # Iter pid = -1 means no iter, 0 means start of iter
        self.iter = -1
        # Proposition?
        self.term = term
        # how to get this term
        self.reason = reason

proofs = [] 

class Proof(object):
    def __init__(self, name, func_declarator, symbol_table):
        self.name = name
        self.func_declarator = func_declarator
        self.proof_list = []
        # w(E, P, T) of the start of the function,
        # an instance of Proof_Term_Context
        self.symbol_table = symbol_table
        # No. of statement list (Q1, Q2, ...)
        self.qid = 0

class Undo(object):
    def __init__(self):
        pass

def handle_semantic(node):
    machine_handler(node)

def build_original_symbol_table(lst):
    table = {}
    if lst == None:
        return table
    for item in lst:
        if item.symbol_type == 'POINTER':
            key = '*' + item.value[0].value[0]
        else:
            key = item.value[0]
        if not table.has_key(key):
            table[key] = item
        elif item.symbol_type == 'POINTER' and not table.has_key(key[1:]):
            table[key[1:]] = Node('POINTER',
                                  item.value_type,
                                  None,
                                  [key[1:], None, None])
        else:
            return -1
    return table

def machine_handler(machine):
    if machine.symbol_type == 'MACHINE':
        variables = machine.value[1] + machine.value[3]
        table = build_original_symbol_table(variables)
        if table == '-1':
            print 'Semantic Error in machine_handler 1.'
            return
        sb = compiler_symbol_table.Symbol_Table(machine.value[0],   # ID
                                                machine.value[2],   # invariant
                                                table)              # attribute
        compiler_symbol_table.sb.append(sb)

        function_handler(machine.value[4])  # function list
    else:
        # error
        print 'Semantic Error in machine_handler 2.'

def function_handler(func_list):
    global_sb = compiler_symbol_table.sb[0]
    for func in func_list:
        if func.symbol_type == 'FUNDEF':
            # func -> func_declarator -> func_name
            func_declarator = func.value[0]
            if func_declarator.symbol_type == 'FUN':
                # func_declarator -> func_name
                func_name = func_declarator.value[0]
                if func_name.symbol_type == 'ID':
                    name_str = func_name.value[0]
                    if not global_sb.table.has_key(name_str):
                        # parameters
                        sb1 = build_original_symbol_table(
                                        func_declarator.value[1])
                        # local
                        if func.value[1].symbol_type == 'STATEMENTLIST':
                            sb2 = build_original_symbol_table(
                                            func.value[1].value[1])
                        else:
                            print 'Semantic Error in function_handler 5.'
                            break
                        
                        if sb1 == -1 or sb2 == -1:
                            print 'Semantic Error in functtableion_handler 6.'
                            break

                        sb_parameter = compiler_symbol_table.Symbol_Table(
                                        func_name, None, sb1, global_sb)
                        sb_local = compiler_symbol_table.Symbol_Table(
                                        func_name,
                                        func.value[1].value[0], # local invariant
                                        sb2,
                                        sb_parameter)
                        compiler_symbol_table.sb.append(sb_parameter)
                        compiler_symbol_table.sb.append(sb_local)
                        # None is a placeholder for the future
                        # functions of this func.
                        global_sb.table[name_str] = [
                            sb_local,                   # local symbol table
                            func_declarator.value[1],   # each place of fomal
                                                        # parameters
                            None                        # functions of the func
                            ]

                        # deal with statements
                        statement_handler(name_str,
                                          func_declarator,
                                          func.value[1].value[2] # statementlist
                                          )
                    else:
                        print 'Semantic Error in function_handler 4.'
                        break
                else:
                    print 'Semantic Error in function_handler 3.'
                    break
            else:
                print 'Semantic Error in function_handler 2.'
                break
        else:
            print 'Semantic Error in function_handler 1.'
            break

# func_name is used for targeting symbol table
def statement_handler(func_name, func_declarator, statement_list):
    symbol_table = compiler_symbol_table.sb[0].table[func_name][0]
    func_table = Proof_Term_Context(
                                    symbol_table.upper_table.upper_table,
                                    symbol_table.upper_table,
                                    symbol_table)
    proof = Proof(func_name, func_declarator, func_table)
    proof.proof_list.append(
        Proof_Term(1,Proposition(symbol_table = func_table,
                                 expression = statement_list,
                                 prop_type = 'STATEMENT'),
                   None))
    proofs.append(proof)

if __name__ == '__main__':
    f = open('test.txt', 'r')
    m = compiler_parser.Proof_Parser()
    x = m.run(''.join(f.readlines()))
    f.close()
    handle_semantic(x)

    a = proofs[0]
    c = a.proof_list[0].term.context
    print c.get_symbol('size', a)
    

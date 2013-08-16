'''
# Now this project has been published in github.
#
#
#
#
#
# Author: Angel An.
# All right reserved.
'''

from compiler_symbol_table import Node, Proposition_Node
from compiler_manual_paser import Manual_Proof_Parser
import compiler_semantic
import copy

class Tactics(object):
    def __init__(self):
        pass

class Statement_Tactics(Tactics):
    def __init__(self):
        super(Tactics, self).__init__()
    
    # find ID
    def walk(self, node, func):
        queue, result = [node], []
        while queue:
            tmp = queue.pop(0)
            # following is an example of hard code, not recomended.
            if func(tmp):
                result.append(tmp)
            elif isinstance(tmp, Node):
                queue.extend(tmp.value)
        return result

    def funcall(self, func_node, func_in_symbol_table):
        # name is ID, value is para_list
        name, actual_para = func_node.value
        func_table, formal_para, opeartion = func_in_symbol_table

        # do something using operations
        pass

    # symbol_table may be a proof_term_context
    # symbol_table_func = lambda x: symbol_table.get_symbol(x, proof)
    def eval_expression(self, exp, symbol_table_func, proof = None):
        #exp = copy.deepcopy(exp)
        while exp.symbol_type == 'EXPRESSION':
            exp = exp.value[0]
        # for const values
        if exp.symbol_type == 'CONST':
            return exp
        elif exp.symbol_type == 'POINTER':
            # result is a vector [value, address]
            s_type, result, scope = symbol_table_func(exp.value[0])
            if (len(result) == 0 and scope != 't') or exp.operation == 'ITER':
                if isinstance(s_type, str):
                    exp.value_type = s_type
                elif not s_type[0] in ('int', 'double', 'char', 'string'):
                    exp.value_type = s_type[0]
                else:
                    exp.value_type = {'int': 'NUMBER',
                                      'double': 'RNUMBER',
                                      'char': 'CHAR',
                                      'string': 'STRING'}[s_type[0]]
                return exp
            elif len(result) == 0 and scope != 'p':
                print 'Using a variable not assignmented.'
                return exp
            return result[0]
        elif exp.symbol_type == 'ID':
            #print 'into...', exp.value[0]
            s_type, result, scope = symbol_table_func(exp.value[0])
            #print result, exp.value
            if (result == None and scope != 't') or exp.operation == 'ITER':
                if isinstance(s_type, str):
                    exp.value_type = s_type
                elif not s_type[0] in ('int', 'double', 'char', 'string'):
                    exp.value_type = s_type[0]
                else:
                    exp.value_type = {'int': 'NUMBER',
                                      'double': 'RNUMBER',
                                      'char': 'CHAR',
                                      'string': 'STRING'}[s_type[0]]
                return exp
            elif result == None and scope != 'p':
                print 'Using a variable not assignmented.'
                return exp
            if isinstance(result, list):
                return result[-1]
            return result
        elif exp.symbol_type == 'FUNC':
            # function is a term (instance of compiler_semantic.Proposition)
            tmp, fpara, function = symbol_table_func(exp.value[0].value[0])[0]
            rpara = exp.value[1]
            function = copy.deepcopy(function)
            for idx in xrange(len(fpara)):
                #print fpara[idx].value[0], function.context.p.table
                #print function.context.p.table[fpara[idx].value[0]]
                function.context.p.table[fpara[idx].value[0]] = rpara[idx]
                #symbol_table_func(fpara[idx].value[0])[0] = rpara[idx]
            result = self.eval_expression(function.expression,
                            lambda x: function.context.get_symbol(x, function))
            return result
        elif exp.symbol_type == 'MATH':
            left, right = self.eval_expression(exp.value[0], symbol_table_func), \
                          self.eval_expression(exp.value[1], symbol_table_func)

            #print left.symbol_type, left.value, '111', left.operation
            
            cast_table = { None: 16,
                          'STRING': 8,
                          'RNUMBER': 4, 'NUMBER': 2, 'CHAR': 1}
            # print exp.value[0].value, exp.value[1]
            return_type = \
                        cast_table[left.value_type]|cast_table[right.value_type]

            if return_type > 7:
                print 'Error with variable types.'
                return # exit?
            elif return_type == 4:
                exp.value_type = 'RNUMBER'
            elif return_type == 2:
                exp.value_type = 'NUMBER'
            else: # return_type == 1
                exp.value_type = 'CHAR'


            op_table = {'PLUS'  : lambda x, y: x + y,
                        'MINUS' : lambda x, y: x - y,
                        'TIMES' : lambda x, y: x * y,
                        'DIVIDE': lambda x, y: x / y,
                        'MOD'   : lambda x, y: x % y,}
            if left.symbol_type == 'CONST' and right.symbol_type == 'CONST':
                exp.symbol_type = 'CONST'
                exp.value = op_table[exp.operation](left.value, right.value)
            elif left.symbol_type == 'MATH' and right.symbol_type == 'CONST' \
                 and left.value[-1].symbol_type == 'CONST' \
                 and left.operation in ('PLUS', 'MINUS') \
                 and exp.operation in ('PLUS', 'MINUS'):
                op = {'PLUS'  : lambda x, y: x - y,
                      'MINUS' : lambda x, y: x + y}
                if left.operation == 'PLUS':
                    left.value[-1].value = \
                        op_table[exp.operation](left.value[-1].value, right.value)
                elif left.operation == 'MINUS':
                    left.value[-1].value = \
                        op[exp.operation](left.value[-1].value, right.value)
                return left
            else:
                exp.value = [left, right]

            return exp
        else: # Proposition, Set, Tuple
            return exp
    
    def handle_statement(self, _term, proof, manual = None):
                         #proof, pid):
        '''proof_term = copy.deepcopy(proof.proof_list[pid])
        proof_term.pid = pid + 1
        term = proof_term.term'''

        term = copy.deepcopy(_term)
        if term.prop_type != 'STATEMENT':
            print 'Error using Statement_Tactics.'
            return

        exp = term.expression.pop(0)
        while exp.symbol_type == 'EXPRESSION':
            exp = exp.value[0]

        if exp.symbol_type == 'ASSIGNMENT':
            # deal with left value
            left, right = exp.value
            if manual:
                right = manual
            symbol_table_func = lambda x: term.context.get_symbol(x, proof)
            if left.symbol_type == 'POINTER':
                left_key = '*' + left.value[0].value[0]
            else:
                left_key = left.value[0]
            #print left_key
            #left_val, scope = term.context.get_symbol(left_key, proof)
            s_type, left_val, scope = symbol_table_func(left_key)
            #print s_type, left_val, scope

            pointer = False
            if left.symbol_type == 'POINTER':
                pointer = True

            #deal with right value
            right_result = self.eval_expression(right, symbol_table_func)

            '''print 'sssssssssssssssssssss'
            print right.symbol_type, right.value[0].value, right.value[1].value
            print left_key, right_result.value[1].symbol_type, \
                  right_result.symbol_type
            print right.value[0].value, right_result.value
            print 'ddddddddddddddddddddd'''

            tmp = {'e': term.context.e.table,
                   'p': term.context.p.table,
                   't': term.context.t.table}[scope]
            lk = ''
            if left.symbol_type == 'POINTER' and left_key[0] != '*':
                lk = left_key
            else:
                '*' + left_key
            if left.symbol_type == 'POINTER' and not tmp.has_key(left_key):
                tmp[lk] = [None, None]
            if tmp.has_key(left_key) and pointer:
                tmp[lk][0] = copy.deepcopy(right_result)
            elif tmp.has_key(left_key) and not pointer:
                tmp[left_key][1] = copy.deepcopy(right_result)
            else:
                tmp[left_key] = copy.deepcopy(right_result)

            # used for confirm if the same w(i?) in proof
            term.context.change_time += 1

            proof.qid = proof.qid + 1
            term.qid = proof.qid

            
        elif exp.symbol_type == 'SELECTION':
            # [if P then S1 else S2]Q
            P, S1, S2 = exp.value
            #print 'Hello, World', S1, S1.symbol_type, S1.value
            Q1, Q2 = term.expression, copy.deepcopy(term.expression)
            #Q1.insert(0, S1)
            #Q2.insert(0, S2)
            S1 = copy.deepcopy(S1.value[-1])
            if S2:
                if S2.symbol_type != 'STATEMENTLIST':
                    S2 = [copy.deepcopy(S2)]
                else:
                    S2 = copy.deepcopy(S2.value[-1])
            Q1 = S1 + Q1
            if S2:
                Q2 = S2 + Q2
            T1, T2 = copy.deepcopy(_term), copy.deepcopy(_term)
            T1.expression, T2.expression = Q1, Q2
            proof.qid = proof.qid + 1
            T1.qid = proof.qid
            proof.qid = proof.qid + 1
            T2.qid = proof.qid
            NP = Proposition_Node('PROPOSITION', None, 'NOT',
                                  [copy.deepcopy(P)])
            new_expression = Proposition_Node('PROPOSITION',
                                              None,
                                              'CONJUNCTION',
                                              [
                               Proposition_Node('PROPOSITION',
                                                None,
                                                'IMPLICATION',
                                                [P, T1]),
                               Proposition_Node('PROPOSITION',
                                                None,
                                                'IMPLICATION',
                                                [NP, T2])])
            # return new_expression
            term.expression = new_expression
            term.prop_type = 'PROPOSITION'
        elif exp.symbol_type == 'ITER':
            # [iter S]Q
            S = copy.deepcopy(exp.value)
            
            Q = term.expression
            Q.insert(0, exp)
            Q = S + Q
            term.expression = Q

            proof.qid = proof.qid + 1
            term.qid = proof.qid
        elif exp.symbol_type == 'ITERATION':
            # [while(P)S]Q
            # return (term1, term2, term3)
            P, S = exp.value
            Q = term.expression
            S.symbol_type = 'ITER'
            S.value = S.value[-1]
            
            tmp1, tmp2 = copy.deepcopy(term), copy.deepcopy(term)
            tmp1.qid, tmp2.qid = proof.qid + 1, proof.qid + 2
            proof.qid += 2
            tmp1.expression, tmp2.expression = [S], Q
            E1 = Proposition_Node('PROPOSITION', None, 'IMPLICATION',
                                  [copy.deepcopy(P), copy.deepcopy(tmp1)])
            E2 = Proposition_Node('PROPOSITION', None, 'IMPLICATION',
                                  [copy.deepcopy(tmp1),
                                   copy.deepcopy(tmp2)])
                                   #Proposition_Node('PROPOSITION', None, 'NOT',
                                    #                [copy.deepcopy(P)])])
            E3 = Proposition_Node('PROPOSITION', None, 'IMPLICATION',
                                  [Proposition_Node('PROPOSITION', None, 'NOT',
                                                    [copy.deepcopy(P)]),
                                   tmp2])

            T1, T2, T3 = copy.deepcopy(_term), copy.deepcopy(_term), \
                         copy.deepcopy(_term)

            

            T1.expression, T2.expression, T3.expression = E1, E2, E3
            #T1.qid, T2.qid, T3.qid = range(proof.qid + 1, proof.qid + 4)
            #proof.qid += 3
            T1.prop_type = T2.prop_type = T3.prop_type = 'PROPOSITION'

            return (T1, T2, T3)
            




            '''
            # Just one step
            # [while(P)S]Q
            P, S = exp.value
            Q1, Q2 = term.expression, copy.deepcopy(term.expression)
            Q1.insert(0, exp)
            #Q1.insert(0, S)
            #tmp1, tmp2 = copy.deepcopy(S.value[-1]), copy.deepcopy(S.value[-1])
            Q1 = S.value[-1] + Q1
            Q2 = S.value[-1] + Q2
            T1, T2 = copy.deepcopy(_term), copy.deepcopy(_term)
            T1.expression, T2.expression = Q1, Q2
            
            proof.qid = proof.qid + 1
            T1.qid = proof.qid
            proof.qid = proof.qid + 1
            T2.qid = proof.qid
            NP = Proposition_Node('PROPOSITION', None, 'NOT',
                                  [copy.deepcopy(P)])
            new_expression = Proposition_Node('PROPOSITION',
                                              None,
                                              'CONJUNCTION',
                                              [
                               Proposition_Node('PROPOSITION',
                                                None,
                                                'IMPLICATION',
                                                [P, T1]),
                               Proposition_Node('PROPOSITION',
                                                None,
                                                'IMPLICATION',
                                                [NP, T2])])
            term.expression = new_expression
            term.prop_type = 'PROPOSITION'''

            
        elif exp.symbol_type == 'JUMP':

            #print term.context.p.table['uwpVMID'].value, 123123
            
            symbol_table_func = lambda x: term.context.get_symbol(x, proof)
            result = self.eval_expression(exp.value[0], symbol_table_func)
            if result.symbol_type == 'PROPOSITION':
                term.prop_type = 'PROPOSITION'
            else:
                term.prop_type = 'MATH'
            changed_e_p = copy.deepcopy(proof.symbol_table)
            changed_e_p.e.table = changed_e_p.update_context(changed_e_p.e,
                                                       term.context.e)
            changed_e_p.p.table = changed_e_p.update_context(changed_e_p.p,
                                                       term.context.p)
            #term.context = changed_e_p

            #print term.context.e.table, 123123

            result = Node('ASSIGNMENT', None, None, ['RETURN', result])
            tmp_table = copy.deepcopy(term.context.t.table)
            tmp_table.update(term.context.p.table)
            for key in tmp_table:
                node = Node('ASSIGNMENT', None, None, [key, tmp_table[key]])
                #print key, tmp_table[key]
                result = Proposition_Node('PROPOSITION', None, 'CONJUNCTION',
                                          [result, node])
            
            term.expression = result # lack of global variables.
            
        elif exp.symbol_type == 'FUNC':
            result = self.eval_expression(exp, symbol_table_func, proof)

        return term

class Math_Tactics(Tactics):
    pass

class Proposition_Tactics(Tactics):
    pass
    # atom, theory, premise, mp, same, inductive assumption
    def same_prop(self, lterm, rterm):
        result = True
        if type(lterm) != type(rterm):
            return False
        if isinstance(lterm, Node):
            result = result and lterm.symbol_type == rterm.symbol_type
            result = result and lterm.value_type == rterm.value_type
            result = result and lterm.operation == rterm.operation

            if isinstance(lterm.value, list):
                if len(lterm.value) != len(rterm.value):
                    result = False
                else:
                    for i in xrange(len(lterm.value)):
                        result = result and self.same_prop(
                                                lterm.value[i], rterm.value[i])
            else:
                result = result and self.same_prop(lterm.value, rterm.value)

            return result
        elif isinstance(lterm, compiler_semantic.Proposition):
            result = result and lterm.prop_type == rterm.prop_type
            '''result = result and \
                     lterm.context.change_time == rterm.context.change_time
            result = result and \
                lterm.symbol_table.change_time == rterm.symbol_table.change_time
            '''
            result = result and self.same_prop(lterm.expression,
                                               rterm.expression)
            return result
        elif isinstance(lterm, list):
            if len(lterm) != len(rterm):
                result = False
            else:
                for i in xrange(len(lterm)):
                    result = result and self.same_prop(lterm[i], rterm[i])
            return result
        else:
            return lterm == rterm
            
    def alike_prop(atom, prop):
        p_map = {}
        atom_stack, prop_stack = [atom], [prop]
        result = True
        while atom_stack and prop_stack:
            a_cur, p_cur = atom_stack.pop(0), prop_stack.pop(0)
            # something has to be done?
            sb_type = a_cur.symbol_type
            if sb_type == 'ID':
                if not p_map.has_key(a_cur.value[0]):
                    p_map[a_cur.value[0]] = p_cur
                else:
                    result = result and self.same_prop(p_map[a_cur.value[0]],
                                                       p_cur)
            else: # ->|~|/\|\/|...
                result = result and (a_cur.operation == p_cur.operation)

            atom_stack.extend(a_cur.value)
            prop_stack.extend(p_cur.value)

        if atom_stack or prop_stack:
            result = False

        return result

    def mp_method(self, prop, sub):
        if isinstance(prop, compiler_semantic.Proposition) and \
           isinstance(prop.expression, Node) and \
           prop.expression.operation == 'IMPLICATION':
            left, right = prop.expression.value
            if self.same_prop(left, sub):
                right.update_context(left.context)
                return right
        return None

    def ab_bc_ac_method(self, ab, bc):
        if isinstance(ab, compiler_semantic.Proposition) and \
            isinstance(ab.expression, Node) and \
            ab.expression.operation == 'IMPLICATION' and \
           isinstance(bc, compiler_semantic.Proposition) and \
            isinstance(bc.expression, Node) and \
            bc.expression.operation == 'IMPLICATION':
            a, b1 = ab.expression.value
            b2, c = bc.expression.value

            #print b1.expression[0].value[0].value[0].value, b2.expression
            
            if self.same_prop(b1, b2):
                tmp_c = copy.deepcopy(c)
                tmp_c.update_context(b1.context)
                result =  compiler_semantic.Proposition(
                                prop_type = 'PROPOSITION',
                                expression = Node('PROPOSITION',
                                                  None,
                                                  'IMPLICATION',
                                    [copy.deepcopy(a), tmp_c]))
                result.context = copy.deepcopy(bc.context)
                result.update_context(b1.context)
                result.symbol_table = copy.deepcopy(bc.symbol_table)
                return result
        return None

    def induction_method(self):
        pass

    def add_proof_term(self, proof, proof_term):
        proof_term.pid = len(proof.proof_list) + 1
        proof.proof_list.append(proof_term)

    def print_proof_term(self, proof_term, v_list = [], \
                         proof = None, iter_id = '', context = None):
        pid, iter_id, term, reason = \
             proof_term.pid, proof_term.iter, proof_term.term, proof_term.reason
        if iter_id >= 0:
            result = 'A%d_%d = %s --- Reason: %s' \
                     %(pid, iter_id,
                       self.ppt_helper(term, proof = proof, context = context),
                       reason)
        else:
            result = 'A%d = %s --- Reason: %s' \
                     %(pid,
                       self.ppt_helper(term, proof = proof, context = context),
                       reason)
        return result

    def get_id_list(self, exp):
        if isinstance(exp, Node):
            if exp.symbol_type == 'ID':
                return set([exp.value[0]])
            else:
                id_set = set()
                for item in exp.value:
                    id_set = id_set.union(self.get_id_list(item))
                return id_set
        else:
            return set()

    def ppt_helper(self, term, v_list = [], proof = None,
                   iter_id = '', context = None):
        result = ''
        if isinstance(term, compiler_semantic.Proposition) and \
           term.prop_type == 'STATEMENT':
            exp = term.expression

            #print type(term), term.expression
            s0, r0 = exp[0], ''
            if s0.symbol_type == 'EXPRESSION':
                while s0.symbol_type == 'EXPRESSION':
                    s0 = s0.value[0]
                if s0.symbol_type != 'ASSIGNMENT':
                    print 'ERROR', s0.symbol_type
                left, right = \
                      self.ppt_helper(s0.value[0], v_list, proof, iter_id,
                                      context = context), \
                      self.ppt_helper(s0.value[1], v_list, proof, iter_id,
                                      context = context)
                r0 = '%s = %s' %(left, right)
            elif s0.symbol_type == 'SELECTION':
                condition = self.ppt_helper(s0.value[0], v_list, proof, iter_id,
                                            context = context)
                if len(s0.value) == 3:
                    r0 = 'if%s{...}else{...}' %condition
                else:
                    r0 = 'if%s{...}' %condition
            elif s0.symbol_type == 'JUMP':
                tmp = self.ppt_helper(s0.value[0], v_list, proof, iter_id,
                                      context = context)
                r0 = 'return %s' %tmp
            
            str_v = ''
            id_list = list(self.get_id_list(s0))
            for key in v_list + id_list:
                if context:
                    v_type, v, scope = \
                            term.context.get_symbol(key, context)
                    #print 'Hello, world!', key, context.context.p.table
                    #if context.context.p.table.has_key('uwpVMID'):
                    #    print context.context.p.table['uwpVMID'].symbol_type
                else:
                    v_type, v, scope = \
                        term.context.get_symbol(key, proof)
                
                itid = ''
                if iter_id == '':
                    pass
                elif iter_id.isdigit():
                    if int(iter_id) == 0:
                        itid = '0'
                    else:
                        itid = iter_id
                elif iter_id[-2:] == '-1':
                    itid = iter_id[0]
                else:
                    itid = iter_id + '+1'
                    
                tmp = self.ppt_helper(v, v_list, proof, iter_id,
                                      context = context)
                #str_v += key + str(iter_id) if tmp == '' else tmp + '; '
                    
                str_v += key + itid \
                         + ' = ' \
                         + (tmp if tmp != '' else key + '0')\
                         + '; '
            result = 'w(%s){%s; Q%d}' %(str_v, r0, term.qid)
        elif isinstance(term, compiler_semantic.Proposition) or \
             isinstance(term, Node):
            exp = None
            if isinstance(term, Node):
                exp = term
            else:
                exp = term.expression
                
            if exp.symbol_type == 'EXPRESSION':
                result = self.ppt_helper(exp.value[0])
            elif exp.symbol_type == 'MATH':
                op_table = {'PLUS': '+', 'MINUS': '-',
                            'TIMES': '*', 'DIVIDE': '/', 'MOD': '%'}
                left, right = \
                      self.ppt_helper(exp.value[0], v_list, proof, iter_id,
                                      context = context), \
                      self.ppt_helper(exp.value[1], v_list, proof, iter_id,
                                      context = context)
                prior = {None: 4, 'PLUS': 1, 'MINUS': 1,
                         'TIMES': 2, 'DIVIDE': 2, 'MOD': 3}
                if exp.operation in ('PLUS', 'TIMES'):
                    if prior[exp.value[0].operation] < prior[exp.operation]:
                        left = '(' + left + ')'
                    if prior[exp.value[1].operation] < prior[exp.operation]:
                        right = '(' + right + ')'
                else:
                    if prior[exp.value[0].operation] < prior[exp.operation]:
                        left = '(' + left + ')'
                    if exp.value[1].operation != None:
                        right = '(' + right + ')'
                result = '%s %s %s' %(left, op_table[exp.operation], right)
            elif exp.symbol_type == 'SET':
                pass
            elif exp.symbol_type == 'TUPLE':
                pass
            elif exp.symbol_type == 'ARRAY':
                pass
            elif exp.symbol_type == 'STRUCT':
                if len(exp.value) == 2:
                    result = '%s.<%s>' %tuple(exp.value)
                else:
                    result = '%s.<%s:%s>' %tuple(exp.value)
            elif exp.symbol_type == 'STRUCT_POINTER':
                result = '%s.<%s:*%s>' %tuple(exp.value)
            elif exp.symbol_type == 'FUNC':
                result = self.ppt_helper(exp.value[0], v_list, proof, iter_id,
                                         context = context)
                result += '('
                for item in exp.value[1]:
                    tmp = self.ppt_helper(item, v_list, proof, iter_id,
                                          context = context)
                    result = '%s%s, ' %(result, tmp)
                result = result[:-2] if exp.value[1] else result
                result += ')'
            elif exp.symbol_type == 'ASSIGNMENT':
                left, right = \
                      self.ppt_helper(exp.value[0], v_list, proof, iter_id,
                                      context = context), \
                      self.ppt_helper(exp.value[1] if not isinstance(exp.value[1], list) else exp.value[1][0]
                                      , v_list, proof, iter_id,
                                      context = context)
                #if isinstance(exp.value[1], list):
                #    print exp.value[1][0].symbol_type
                result = '%s = %s' %(left, right)
            elif exp.symbol_type == 'ID':
                #print 123, exp.value
                if iter_id.isdigit():
                    return exp.value[0] + '0'#str(iter_id)
                elif iter_id != '':
                    return exp.value[0] + iter_id
                elif isinstance(exp.value[1], str):
                    return exp.value[1]
                else:
                    return exp.value[0]
            elif exp.symbol_type == 'POINTER':
                #print exp, exp.value[0].symbol_type, exp.value[0].value
                if iter_id.isdigit():
                    return '*' + exp.value[0].value[0] + '0'
                elif iter_id != '':
                    return '*' + exp.value[0].value[0] + iter_id
                elif isinstance(exp.value[1], str):
                    return exp.value[1]
                else:
                    return '*' + exp.value[0].value[0]
            elif exp.symbol_type == 'CONST':
                #print exp.value, exp.symbol_type, exp.value_type
                return str(exp.value)
            elif exp.symbol_type == 'PROPOSITION':
                op_table = {'CONJUNCTION': '/\\', 'DISJUNCTION': '\\/',
                            'IMPLICATION': '->', 'NOT': '~',
                            'FORALL': '#', 'EXIST': '!',
                            'LESS': '<', 'LESSEQUAL': '<=',
                            'GREATER': '>', 'GREATEQUAL': '>=',
                            'EQUAL': '==', 'NOTEQUAL': '!=',
                            'BELONGTO': ':', 'NOTBELONGTO': '!:'}
                if exp.operation in ('FORALL', 'EXIST', 'NOT'):
                    left, right = '', self.ppt_helper(exp.value[0], v_list,
                                                      proof, iter_id,
                                                      context = context)
                    result = '%s(%s)' %(op_table[exp.operation], right)
                else:
                    #print exp.value[0].symbol_type, exp.value[1]
                    left = self.ppt_helper(exp.value[0], v_list, proof, iter_id,
                                          context = context)
                    #print op_table[exp.operation], exp.value[1], type(exp.value[1])
                    if isinstance(exp.value[1], str):
                        right = exp.value[1]
                    else:
                        #print op_table[exp.operation]
                        right = self.ppt_helper(exp.value[1],  v_list, proof, iter_id,
                                          context = context)
                    result = '(%s)%s(%s)' \
                             %(left, op_table[exp.operation], right)
        elif term == None:
            pass
        else:
            result = str(term)
        return result

    # sub_str: 'llrrllr' means left, left, right, right, left, left, right
    # return sub and its parent and idx of sub from parent
    def get_sub(self, term, sub_str):
        '''if sub_str == '':
            return term, None, 0
        if isinstance(term, compiler_semantic.Proposition):
            exp = term.expression
        else:
            exp = term
        if exp.symbol_type == 'PROPOSITION':
            if exp.operation == 'NOT':
                return self.get_sub(exp.value[0], sub_str[1:]), exp, 0
            elif sub_str[0] == 'l':
                return self.get_sub(exp.value[0], sub_str[1:]), exp, -1
            else: # sub_str[0] == 'r':
                return self.get_sub(exp.value[-1], sub_str[1:]), exp, -1'''
        return self.__get_sub(term, sub_str, None, 0)

    def __get_sub(self, term, sub_str, parent, idx):
        if sub_str == '':
            return term, parent, idx
        if isinstance(term, compiler_semantic.Proposition):
            exp = term.expression
        else:
            exp = term
        if exp.symbol_type == 'PROPOSITION':
            if exp.operation == 'NOT':
                return self.__get_sub(exp.value[0], sub_str[1:], exp, 0)
            elif sub_str[0] == 'l':
                return self.__get_sub(exp.value[0], sub_str[1:], exp, -1)
            else: # sub_str[0] == 'r':
                return self.__get_sub(exp.value[-1], sub_str[1:], exp, -1)

    def update_sub(self, term, sub, sub_str):
        if sub_str == '':
            return sub
        if isinstance(term, compiler_semantic.Proposition):
            exp = term.expression
            if sub_str[0] == 'l':
                term.expression.value[0] = self.update_sub(exp.value[0],
                                                           sub, sub_str[1:])
            else:
                term.expression.value[-1] = self.update_sub(exp.value[-1],
                                                           sub, sub_str[1:])
        else:
            exp = term
            if sub_str[0] == 'l':
                term.value[0] = self.update_sub(exp.value[0],
                                                           sub, sub_str[1:])
            else:
                term.value[-1] = self.update_sub(exp.value[-1],
                                                           sub, sub_str[1:])
        return term
        

class Tactic_Router():
    def __init__(self):
        self.stac = Statement_Tactics()
        self.mtac = Math_Tactics()
        self.ptac = Proposition_Tactics()

    def get_sub(self, proof, proof_term, sub_str = ''):
        new_pt = compiler_semantic.Proof_Term()
        new_pt.term = copy.deepcopy(proof_term.term)
        new_pt.reason = 'Sub %s of A%d' %(sub_str, proof_term.pid)
        sub, parent, idx = self.ptac.get_sub(new_pt.term, sub_str)
        new_pt.term = sub
        self.ptac.add_proof_term(proof, new_pt)
        print ptac.print_proof_term(new_pt, proof = proof)

    def handle_statement(self, proof, proof_term, sub_str = '', manual = None):
        new_pt = compiler_semantic.Proof_Term()
        new_pt.term = copy.deepcopy(proof_term.term)
        new_pt.reason = 'Read a statement.'
        sub, parent, idx = self.ptac.get_sub(new_pt.term, sub_str)

        sub = self.stac.handle_statement(sub, proof, manual)
        '''print sub
        if sub.context.p.table.has_key('uwpVMID'):
            print 123123123, sub.context.p.table['uwpVMID'].value'''
        
        if isinstance(sub, compiler_semantic.Proposition):
            if parent:
                parent.value[idx] = sub
            else:
                new_pt.term = sub

            self.ptac.add_proof_term(proof, new_pt)
            print self.ptac.print_proof_term(new_pt, proof = proof,
                                             context = sub)
        else:
            for prop in sub:
                pt = compiler_semantic.Proof_Term()
                pt.term = prop
                self.ptac.add_proof_term(proof, pt)
                print self.ptac.print_proof_term(pt, proof = proof,
                                                 context = prop)

    def ab_bc_ac_method(self, proof, ab_term, bc_term):
        new_pt = compiler_semantic.Proof_Term()
        #new_pt.term = copy.deepcopy(proof_term.term)
        new_pt.reason = \
            'A -> B, B ->C |- A -> C    A%d, A%d' %(ab_term.pid, bc_term.pid)
        new_pt.term = self.ptac.ab_bc_ac_method(ab_term.term, bc_term.term)
        self.ptac.add_proof_term(proof, new_pt)
        print self.ptac.print_proof_term(new_pt, proof = proof)

    def mp_method(self, proof, ab, a):
        new_pt = compiler_semantic.Proof_Term()
        new_pt.reason = 'A -> B, A |- B    A%d, A%d' %(ab.pid, a.pid)
        new_pt.term = self.ptac.mp_method(ab.term, a.term)
        self.ptac.add_proof_term(proof, new_pt)
        print self.ptac.print_proof_term(new_pt, proof = proof)

    '''def mp_method(self, prop, sub):
        if isinstance(prop, compiler_semantic.Proposition) and \
           isinstance(prop.expression, Node) and \
           prop.expression.operation == 'IMPLICATION':
            left, right = prop.expression.value
            if self.same_prop(left, sub):
                right.update_context(left.context)
                return right
        return None'''

    def split_method(self, proof, a, sub_str = ''):
        sub, parent, idx = self.ptac.get_sub(a.term, sub_str)
        
        new_pt_l, new_pt_r = compiler_semantic.Proof_Term(), \
                             compiler_semantic.Proof_Term()
        new_pt_l.reason = 'Split l, A%d' %a.pid
        new_pt_r.reason = 'Split r, A%d' %a.pid
        left, right = None, None
        if isinstance(sub, compiler_semantic.Proposition) and \
           isinstance(sub.expression, Node) and \
           sub.expression.operation == 'CONJUNCTION':
            left, right = sub.expression.value
        if not sub_str:
            new_pt_l.term, new_pt_r.term = left, right
        else:
            new_pt_l.term, new_pt_r.term = copy.deepcopy(a.term), \
                                           copy.deepcopy(a.term)
            new_pt_l.term = self.ptac.update_sub(new_pt_l.term, left, sub_str)
            new_pt_r.term = self.ptac.update_sub(new_pt_r.term, right, sub_str)
            
        self.ptac.add_proof_term(proof, new_pt_l)
        self.ptac.add_proof_term(proof, new_pt_r)

        print self.ptac.print_proof_term(new_pt_l, proof = proof)
        print self.ptac.print_proof_term(new_pt_r, proof = proof)

    def imp_conj_method(self, proof, a):
        '''A -> B ->C |- A /\ B -> C'''
        new_pt = compiler_semantic.Proof_Term()
        new_pt.reason = 'A -> B ->C |- A /\ B -> C    A%d' %a.pid
        new_pt.term = copy.deepcopy(a.term)
        if new_pt.term.operation == 'IMPLICATION' and \
           new_pt.term.value[-1].operation == 'IMPLICATION':
            left, right = new_pt.term.value
            new_pt.term.value[0] = Node('PROPOSITION', None, 'CONJUNCTION',
                                             [left, right.value[0]])
            new_pt.term.value[-1] = right.value[-1]
            self.ptac.add_proof_term(proof, new_pt)
            print self.ptac.print_proof_term(new_pt, proof = proof)

    def print_method(self, proof, a):
        print self.ptac.print_proof_term(a, proof = proof)

    def start_inductive(self, proof, proof_term,
                        iter_id, sub_str = '', v_list = []):
        sub, parent, idx = self.ptac.get_sub(proof_term.term, sub_str)
        '''for key in v_list:
            v_type, v, scope = proof_term.term.context.get_symbol(key, proof)
            node = Node('ID', v_type, None, [key, None])
            if scope == 'e':
                proof_term.term.context.e.table[key].symbol_type = 'ID'                
                proof_term.term.context.e.table[key].value = [key, node]
            elif scope == 'p':
                proof_term.term.context.p.table[key].symbol_type = 'ID'
                proof_term.term.context.p.table[key].value = [key, node]
            elif scope == 't':
                proof_term.term.context.t.table[key].symbol_type = 'ID'
                proof_term.term.context.t.table[key].value = [key, node]'''
        for key in v_list:
            v_type, v, scope = sub.context.get_symbol(key, proof)
            node = Node('ID', v_type, None, [key, None])
            if scope == 'e':
                sub.context.e.table[key].symbol_type = 'ID'                
                sub.context.e.table[key].value = [key, node]
            elif scope == 'p':
                sub.context.p.table[key].symbol_type = 'ID'
                sub.context.p.table[key].value = [key, node]
            elif scope == 't':
                sub.context.t.table[key].symbol_type = 'ID'
                sub.context.t.table[key].value = [key, node]
            

    def inductive(self, proof, proof_term, iter_id, sub_str = '', v_list = []):
        # REDUCE
        '''for key in v_list:
            v_type, v, scope = proof_term.term.context.get_symbol(key, proof)
            str_v = ptac.ppt_helper(v, v_list, proof)
            #str_v = key + str(iter_id) if str_v == '' else str_v
            #print '%s%d = %s' %(key, iter_id, str_v)
            print str_v'''
        itid = ''
        if iter_id.isdigit():
            itid = iter_id
        elif iter_id[-2:] == '-1':
            itid = iter_id[0]
        else:
            itid = iter_id + '+1'
        print 'A_' + itid + ' = ' + \
              self.ptac.ppt_helper(proof_term.term, v_list, proof, iter_id)

    def do_inductive(self, proof, proof_term,
                        iter_id, sub_str = '', v_list = [], changed_list = []):
        '''new_pt = compiler_semantic.Proof_Term()
        new_pt.term = copy.deepcopy(proof_term.term)
        new_pt.reason = 'Do Inductive Statement.'
        print new_pt.term
        sub, parent, idx = self.ptac.get_sub(new_pt.term, sub_str)
        
        sub = self.stac.handle_statement(sub, proof)
        if isinstance(sub, compiler_semantic.Proposition) and \
           sub.prop_type == 'STATEMENT':
            print sub.expression
            sub.expression.pop(0)
            new_pt.term = sub

            self.ptac.add_proof_term(proof, new_pt)
            print ptac.print_proof_term(new_pt)
        else:
            print 'Error in do_inductive.'''
        sub, parent, idx = self.ptac.get_sub(proof_term.term, sub_str)
        for key, value in zip(v_list, changed_list):
            v_type, v, scope = sub.context.get_symbol(key, proof)
            node = Node('ID', v_type, None, [key, value])
            if scope == 'e':
                sub.context.e.table[key].symbol_type = 'ID'                
                sub.context.e.table[key].value = [key, node]
            elif scope == 'p':
                sub.context.p.table[key].symbol_type = 'ID'
                sub.context.p.table[key].value = [key, node]
            elif scope == 't':
                sub.context.t.table[key].symbol_type = 'ID'
                sub.context.t.table[key].value = [key, node]

def test_iter():
    f = open('test.txt', 'r')
    m = compiler_semantic.compiler_parser.Proof_Parser()
    x = m.run(''.join(f.readlines()))
    f.close()
    compiler_semantic.handle_semantic(x)

    a = compiler_semantic.proofs[0]

    tac = Statement_Tactics()
    ptac = Proposition_Tactics()
    tac_r = Tactic_Router()
    
    print ptac.print_proof_term(a.proof_list[0])
    tac_r.handle_statement(a, a.proof_list[0])
    pt1, pt2, sbpt, sbpt2 = a.proof_list
    #tac_r.get_sub(a, sbpt, 'l')
    tac_r.inductive(a, a.proof_list[1], '0', 'r', ['x', 'y'])
    tac_r.handle_statement(a, a.proof_list[1], 'r')
    tac_r.handle_statement(a, a.proof_list[-1], 'r')
    tac_r.handle_statement(a, a.proof_list[-1], 'r')
    tac_r.inductive(a, a.proof_list[-1], '1', 'r', ['x', 'y'])
    for i in xrange(2, 8):
        tac_r.handle_statement(a, a.proof_list[-1], 'r')
        tac_r.handle_statement(a, a.proof_list[-1], 'r')
        tac_r.handle_statement(a, a.proof_list[-1], 'r')
        tac_r.inductive(a, a.proof_list[-1], str(i), 'r', ['x', 'y'])
    tac_r.start_inductive(a, a.proof_list[-1], 'k', 'r', ['x', 'y'])
    tac_r.inductive(a, a.proof_list[-1], 'n', 'r', ['x', 'y'])
    #tac_r.handle_statement(a, a.proof_list[-1], 'r')
    #tac_r.handle_statement(a, a.proof_list[-1], 'r')
    #tac_r.handle_statement(a, a.proof_list[-1])
    tac_r.inductive(a, a.proof_list[-1], 'n-1', '', ['x', 'y'])
    tac_r.inductive(a, a.proof_list[-1], 'n', '', ['x', 'y'])
    tac_r.do_inductive(a, a.proof_list[-1], 'k', 'r',
                          ['x', 'y'], ['0', 'x!'])
    tac_r.inductive(a, a.proof_list[-1], 'n', '', ['x', 'y'])
    #tac_r.do_inductive(a, a.proof_list[-1], '', None, None, None, None)
    tac_r.ab_bc_ac_method(a, a.proof_list[-1], a.proof_list[2])
    tac_r.handle_statement(a, a.proof_list[-1], 'r')
    #tac_r.ab_bc_ac_method(a, a.proof_list[-1], a.proof_list[3])
    tac_r.handle_statement(a, a.proof_list[3], 'r')

def test_real():
    f = open('real.txt', 'r')
    m = compiler_semantic.compiler_parser.Proof_Parser()
    x = m.run(''.join(f.readlines()))
    f.close()
    compiler_semantic.handle_semantic(x)

    a = compiler_semantic.proofs[0]

    tac = Statement_Tactics()
    ptac = Proposition_Tactics()
    tac_r = Tactic_Router()

    print ptac.print_proof_term(a.proof_list[0], proof = a)
    tac_r.handle_statement(a, a.proof_list[-1])
    '''tac_r.handle_statement(a, a.proof_list[-1], 'lr')
    tac_r.handle_statement(a, a.proof_list[-1], 'lr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rrlr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rrrr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rrrrlr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rrrrrr')
    tac_r.handle_statement(a, a.proof_list[-1], 'rrrrrr')'''
    tac_r.split_method(a, a.proof_list[-1])
    tac_r.handle_statement(a, a.proof_list[-2], 'r')
    tac_r.handle_statement(a, a.proof_list[-1], 'r')
    tac_r.handle_statement(a, a.proof_list[-3], 'r')
    tac_r.split_method(a, a.proof_list[-1], 'r')
    tac_r.imp_conj_method(a, a.proof_list[-2])
    tac_r.imp_conj_method(a, a.proof_list[-2])
    tac_r.handle_statement(a, a.proof_list[-2], 'r')
    tac_r.handle_statement(a, a.proof_list[-2], 'r')
    tac_r.split_method(a, a.proof_list[-1], 'r')
    tac_r.imp_conj_method(a, a.proof_list[-2])
    tac_r.imp_conj_method(a, a.proof_list[-2])
    tac_r.handle_statement(a, a.proof_list[-2], 'r')
    tac_r.handle_statement(a, a.proof_list[-2], 'r')
    tac_r.handle_statement(a, a.proof_list[-1], 'r')

def console():
    f = open('real.txt', 'r')
    m = compiler_semantic.compiler_parser.Proof_Parser()
    x = m.run(''.join(f.readlines()))
    f.close()
    compiler_semantic.handle_semantic(x)

    a = compiler_semantic.proofs[0]

    tac = Statement_Tactics()
    ptac = Proposition_Tactics()
    tac_r = Tactic_Router()

    print ptac.print_proof_term(a.proof_list[0], proof = a)

    flag = False
    if flag:
        line = 'begin'
        while(line.split()[0] != 'exit'):
            line = raw_input('>>> ')
            worker(line, a, tac, ptac, tac_r)
    else:
        f = open('commands.txt', 'r')
        for line in f:
            print '>>>', line,
            if line .split()[0] == 'exit':
                break
            worker(line, a, tac, ptac, tac_r)
    

def worker(line, a, tac, ptac, tac_r):
    l = line.split()
    a_last = copy.deepcopy(a)
    try:
        if True:
            if l[0] == 'read':
                if len(l) == 3:
                    tmp, idx, sub_str = l
                else:
                    idx = l[-1]
                    sub_str = ''
                idx = int(idx) - 1
                tac_r.handle_statement(a, a.proof_list[idx], sub_str)
            elif l[0] == 'split':
                if len(l) == 3:
                    tmp, idx, sub_str = l
                else:
                    idx = l[-1]
                    sub_str = ''
                idx = int(idx) - 1
                tac_r.split_method(a, a.proof_list[idx], sub_str)
            elif l[0] == 'imp_conj':
                idx = int(l[-1]) - 1
                tac_r.imp_conj_method(a, a.proof_list[idx])
            elif l[0] == 'print':
                idx = int(l[-1]) -1
                tac_r.print_method(a, a.proof_list[idx])
            elif l[0] == 'man':
                m = Manual_Proof_Parser()
                line = raw_input('Imput expression: ')
                x = m.run(line)
                if len(l) == 4:
                    waste, tmp, idx, sub_str = l
                else:
                    idx = l[-1]
                    sub_str = ''
                idx = int(idx) - 1
                tac_r.handle_statement(a, a.proof_list[idx], sub_str, x)
            a_last = copy.deepcopy(a)
    except Exception, e:
        print '>>>', 'Error', e
        a = copy.deepcopy(a_last)

if __name__ == '__main__':
    console()
    #test_real()
    
    







































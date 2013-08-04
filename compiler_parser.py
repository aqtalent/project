import copy
import compiler_lexer
import ply.yacc as yacc
from compiler_symbol_table import Node, Statement_Node, Proposition_Node, \
                                  Set_Node, Tuple_Node, Math_Node

class Parser:
    """
    Base class for a lexer/parser that has the rules defined as methods
    """
    tokens = ()
    precedence = ()

    def __init__(self, **kw):
        self.debug = kw.get('debug', 0)
        self.names = { }
        try:
            modname = os.path.split(os.path.splitext(__file__)[0])[1] + "_" + self.__class__.__name__
        except:
            modname = "parser"+"_"+self.__class__.__name__
        self.debugfile = modname + ".dbg"
        self.tabmodule = modname + "_" + "parsetab"

        # Build the lexer and parser
        #lex.lex(module=self, debug=self.debug)
        compiler_lexer.m.build(debug = self.debug)
        yacc.yacc(module=self,
                  debug=self.debug,
                  debugfile=self.debugfile,
                  tabmodule=self.tabmodule)

    def run(self, data = ''):
        return yacc.parse(data)

    
class Proof_Parser(Parser):

    # Tokens
    
    tokens = compiler_lexer.Lexer.tokens

    # Parsing rules

    precedence = (
        ('nonassoc', 'LESS', 'LESSEQUAL', 'EQUAL',
                     'GREATEREQUAL', 'GREATER', 'NOTEQUAL'),
        ('left','PLUS','MINUS'),
        ('left', 'TIMES', 'DIVIDE'),
        ('left', 'MOD'),
        )

    # Abstract Machine
    def p_abstract_machine_1(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           INVARIANT proposition_conjunction_expression SEMICOLON \
                           ATTRIBUTES declaration_list \
                           OPERATIONS function_definition_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], p[7], p[10], p[12]])
        print 'p_abstract_machine_1'

    def p_abstract_machine_2(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           ATTRIBUTES declaration_list \
                           OPERATIONS function_definition_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], None, p[7], p[9]])
        print 'p_abstract_machine_2'

    def p_abstract_machine_3(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           INVARIANT proposition_conjunction_expression SEMICOLON \
                           OPERATIONS function_definition_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], p[7], None, p[10]])
        print 'p_abstract_machine_3'

    def p_abstract_machine_4(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           INVARIANT proposition_conjunction_expression SEMICOLON \
                           ATTRIBUTES declaration_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], p[7], p[10], None])
        print 'p_abstract_machine_4'

    def p_abstract_machine_5(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           OPERATIONS function_definition_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], None, None, p[7]])
        print 'p_abstract_machine_5'

    def p_abstract_machine_6(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           ATTRIBUTES declaration_list \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], None, p[7], None])
        print 'p_abstract_machine_6'

    def p_abstract_machine_7(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN \
                           INVARIANT proposition_conjunction_expression SEMICOLON \
                           END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], p[7], None, None])
        print 'p_abstract_machine_7'

    def p_abstract_machine_8(self, p):
        'abstract_machine : MACHINE ID LPAREN parameter_type_list RPAREN END'
        p[0] = Node('MACHINE', None, None, [p[2], p[4], None, None, None])
        print 'p_abstract_machine_8'

    # Function Definition List

    def p_function_definition_list_1(self, p):
        'function_definition_list : \
             function_definition_list function_definition'
        p[0] = p[1] + [p[2]]
        print 'p_function_definition_list_1'

    def p_function_definition_list_2(self, p):
        'function_definition_list : function_definition'
        p[0] = [p[1]]
        print 'p_function_definition_list_2'

    # Function Definition

    def p_function_definition_1(self, p):
        'function_definition : declaration_specifiers declarator compound_statement'
        p[0] = Node('FUNDEF', p[1], None, [p[2], p[3]])
        print 'p_function_definition_1'

    def p_function_definition_2(self, p):
        'function_definition : declarator compound_statement'
        p[0] = Node('FUNDEF', 'VOID', None, [p[1], p[2]])
        print 'p_function_definition_2'

    # Declaration List
    
    def p_declaration_list_1(self, p):
        'declaration_list : declaration_list declaration'
        p[0] = p[1] + p[2]
        print 'p_declaration_list_1'

    def p_declaration_list_2(self, p):
        'declaration_list : declaration'
        p[0] = p[1]
        print 'p_declaration_list_2'

    # Declaration
    
    def p_declaration_1(self, p):
        'declaration : declaration_specifiers init_declarator_list SEMICOLON'
        #p[0] = [p[1], p[2]]
        #p[0] = []
        for item in p[2]:
            #p[0].append(Node('ID', p[1], None, item))
            item.value_type = p[1]
        p[0] = p[2]
        print 'p_declaration_1'

    def p_declaration_2(self, p):
        'declaration : declaration_specifiers SEMICOLON'
        p[0] = [p[1]]
        # Useless?
        print 'p_declaration_2'

    # Declaration Specifiers

    def p_declaration_specifiers_1(self, p):
        'declaration_specifiers : type_qualifier type_specifier'
        p[0] = [p[1], p[2]]
        print 'p_declaration_specifiers_1'

    def p_declaration_specifiers_2(self, p):
        'declaration_specifiers : type_specifier'
        p[0] = [p[1]]
        print 'p_declaration_specifiers_2'

    # Type Specifier
    
    def p_type_specifier(self, p):
        '''
        type_specifier : VOID
                       | TYPE_INT
                       | TYPE_FLOAT
                       | TYPE_CHAR
                       | TYPE_STRING
                       | TYPE_BOOL
                       | TYPE_PROPOSITION
                       | TYPE_SET
                       | TYPE_TUPLE
                       | TYPE
                       | ID
        '''
        p[0] = p[1]
        print 'p_type_specifier'

    # Type Qualifier

    def p_type_qualifier(self, p):
        'type_qualifier : CONST'
        p[0] = p[1]
        print 'p_type_qualifier'

    # Init Declarator List

    def p_init_declarator_list_1(self, p):
        'init_declarator_list : init_declarator_list COMMA init_declarator'
        p[0] = p[1] + [p[3]]
        print 'p_init_declarator_list_1'

    def p_init_declarator_list_2(self, p):
        'init_declarator_list : init_declarator'
        p[0] = [p[1]]
        print 'p_init_declarator_list_2'

    # Init Delarator

    def p_init_declarator_1(self, p):
        'init_declarator : declarator'
        # p[1] is an ID?
        p[0] = p[1]
        print 'p_init_declarator_1'

    def p_init_declarator_2(self, p):
        'init_declarator : declarator ASSIGNMENT initializer'
        p[0] = copy.copy(p[1])
        # p[1] is an ID?
        p[0].value[1] = p[3][0]        # ? FIXFIXFIX
        print 'p_init_declarator_2'

    
    # Declarator

    def p_declarator(self, p):
        'declarator : direct_declarator'
        p[0] = p[1]
        print 'p_declarator'

    # Direct Declarator

    def p_direct_declarator_1(self, p):
        'direct_declarator : ID'
        p[0] = Node('ID', None, None, [p[1], None])
        print 'p_direct_declarator_1'

    def p_direct_declarator_2(self, p):
        'direct_declarator : LPAREN declarator RPAREN'
        p[0] = p[1] #Node('FUN', None, None, [p[1], p[2]])
        print 'p_direct_declarator_2'

    def p_direct_declarator_3(self, p):
        'direct_declarator : \
            direct_declarator LBRACKET constant_expression_opt RBRACKET'
        # Useless?
        print 'p_direct_declarator_3'

    def p_direct_declarator_4(self, p):
        'direct_declarator : direct_declarator LPAREN parameter_type_list RPAREN'
        p[0] = Node('FUN', None, None, [p[1], p[3]])
        print 'p_direct_declarator_4'

    def p_direct_declarator_5(self, p):
        'direct_declarator : direct_declarator LPAREN identifier_list RPAREN'
        p[0] = Node('FUN', None, None, [p[1], p[3]])
        print 'p_direct_declarator_5'

    def p_direct_declarator_6(self, p):
        'direct_declarator : direct_declarator LPAREN RPAREN'
        p[0] = Node('FUN', None, None, [p[1], None])
        print 'p_direct_declarator_6'

    def p_direct_declarator_7(self, p):
        'direct_declarator : unary_expression'
        p[0] = p[1]
        print 'p_direct_declarator_6'

    # Constant Expression Opt

    def p_constant_expression_opt_1(self, p):
        'constant_expression_opt : constant_expression'
        p[0] = p[1]
        print 'p_constant_expression_opt_1'

    # Constant Expression

    def p_constant_expression_1(self, p):
        'constant_expression : proposition_implication_expression'
        p[0] = p[1]
        print 'p_constant_expression_1'

    # Parameter Type List
    
    def p_parameter_type_list_1(self, p):
        'parameter_type_list : parameter_list'
        p[0] = p[1]
        # input: parameter_list ([node1, node2, ... , noden])
        # change this list into dict
        
        print 'p_parameter_type_list_1'

    # Parameter List

    def p_parameter_list_1(self, p):
        'parameter_list : parameter_declaration'
        p[0] = [p[1]]
        print 'p_parameter_list_1'

    def p_parameter_list_2(self, p):
        'parameter_list : parameter_list COMMA parameter_declaration'
        p[0] = p[1] + [p[3]]
        print 'p_parameter_list_2'

    # Parameter Declaration

    def p_parameter_declaration_1(self, p):
        'parameter_declaration : declaration_specifiers declarator'
        if p[2].symbol_type == 'ID':#isinstance(p[2], basestring):
            #p[0] = Node('ID', p[1], None, [p[2], None])
            p[2].value_type = p[1]
            p[0] = p[2]
        elif p[2].symbol_type == 'POINTER':
            p[2].value_type = p[1]
            p[0] = p[2]
            print 'This is pointer.'
        else:
            print 'A function in p_parameter_declaration_1?'
        print 'p_parameter_declaration_1'

    # Identifier List

    def p_identifier_list_1(self, p):
        'identifier_list : ID'
        p[0] = [Node('ID', None, None, [p[1], None])]
        print 'p_identifier_list_1'

    def p_identifier_list_2(self, p):
        'identifier_list : identifier_list COMMA ID'
        p[0] = p[1] + [Node('ID', None, None, [p[3], None])]
        print 'p_identifier_list_2'

    # Initializer

    def p_initializer_1(self, p):
        'initializer : assignment_expression'
        p[0] = [p[1]]
        print 'p_initializer_1'

    def p_initializer_2(self, p):
        '''
        initializer : LBRACE initializer_list RBRACE
                    | LBRACE initializer_list COMMA RBRACE
        '''
        p[0] = p[2]
        print 'p_initializer_2'

    # Initializer List

    def p_initializer_list_1(self, p):
        'initializer_list : initializer'
        p[0] = [p[1]]
        print 'p_initializer_list_1'

    def p_initializer_list_2(self, p):
        'initializer_list : initializer_list COMMA initializer'
        p[0] = p[1] + [p[3]]
        print 'p_initializer_list_2'

    # Statement

    def p_statement(self, p):
        '''
        statement : expression_statement
                  | compound_statement
                  | selection_statement
                  | iteration_statement
                  | jump_statement
        '''
        p[0] = p[1]
        print 'p_statement'

    # Expression Statement
    
    def p_expression_statement(self, p):
        'expression_statement : expression_opt SEMICOLON'
        #p[0] = Statement_Node('EXPRESSION', None, None, p[1])
        # Is this right?
        p[0] = p[1]
        print 'p_expression_statement'

    # Compound Statement

    def p_compound_statement_1(self, p):
        'compound_statement : LBRACE \
                              INVARIANT proposition_implication_expression SEMICOLON \
                              ATTRIBUTES declaration_list \
                              statement_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [p[3], p[6], p[7]])
        print 'p_compound_statement_1'

    def p_compound_statement_2(self, p):
        'compound_statement : LBRACE \
                              ATTRIBUTES declaration_list \
                              statement_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [None, p[3], p[4]])
        print 'p_compound_statement_2'

    def p_compound_statement_3(self, p):
        'compound_statement : LBRACE \
                              INVARIANT proposition_implication_expression SEMICOLON \
                              statement_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [p[3], None, p[4]])
        print 'p_compound_statement_3'

    def p_compound_statement_4(self, p):
        'compound_statement : LBRACE \
                              statement_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [None, None, p[2]])
        print 'p_compound_statement_4'

    def p_compound_statement_5(self, p):
        'compound_statement : LBRACE \
                              INVARIANT proposition_implication_expression SEMICOLON \
                              ATTRIBUTES declaration_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [p[3], p[6], None])
        print 'p_compound_statement_5'

    def p_compound_statement_6(self, p):
        'compound_statement : LBRACE \
                              ATTRIBUTES declaration_list \
                              RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [None, p[3], None])
        print 'p_compound_statement_6'

    def p_compound_statement_7(self, p):
        'compound_statement : LBRACE RBRACE'
        p[0] = Statement_Node('STATEMENTLIST', None, None, [None, None, None])
        print 'p_compound_statement_7'

    # Statement List
    
    def p_statement_list_1(self, p):
        'statement_list : statement'
        p[0] = [p[1]]
        print 'p_statement_list_1'

    def p_statement_list_2(self, p):
        'statement_list : statement_list statement'
        p[0] = p[1] + [p[2]]
        print 'p_statement_list_2'

    # Selection Statement

    def p_selection_statement_1(self, p):
        'selection_statement : IF LPAREN expression RPAREN statement'
        p[0] = Statement_Node('SELECTION', None, None, [p[3], p[5], None])
        print 'p_selection_statement_1'

    def p_selection_statement_2(self, p):
        'selection_statement : \
             IF LPAREN expression RPAREN statement ELSE statement'
        p[0] = Statement_Node('SELECTION', None, None, [p[3], p[5], p[7]])
        print 'p_selection_statement_2'

    # Iteration Statement

    def p_iteration_statement(self, p):
        'iteration_statement : WHILE LPAREN expression RPAREN statement'
        p[0] = Statement_Node('ITERATION', None, None, [p[3], p[5]])
        print 'p_iteration_statement'

    # Jump Statement

    def p_jump_statement(self, p):
        'jump_statement : RETURN expression_opt SEMICOLON'
        p[0] = Statement_Node('JUMP', None, None, [p[2]])
        print 'p_jump_statement'

    # Expression Opt

    def p_expression_opt_1(self, p):
        'expression_opt : expression'
        p[0] = p[1]
        print 'p_expression_opt_1'

    '''def p_expression_opt_2(self, p):
        'expression_opt : expression'
        pass'''

    # Expression

    def p_expression_1(self, p):
        'expression : expression_list'
        p[0] = Node('EXPRESSION', None, None, p[1])
        print 'p_expression_1'

    '''def p_expression_2(self, p):
        'expression : expression COMMA assignment_expression'
        p[0] = p[1] + [p[3]]
        print 'p_expression_2'''

    def p_expression_list_1(self, p):
        'expression_list : assignment_expression'
        p[0] = [p[1]]
        print 'p_expression_list_1'

    def p_expression_list_2(self, p):
        'expression_list : expression_list COMMA assignment_expression'
        p[0] = p[1] + [p[3]]

    # Assignment Expression

    def p_assignment_expression_1(self, p):
        'assignment_expression : proposition_implication_expression'
        p[0] = p[1]
        print 'p_assignment_expression_1'

    def p_assignment_expression_2(self, p):
        'assignment_expression : \
            unary_expression assignment_operator assignment_expression'
        p[0] = Node('ASSIGNMENT', None, 'ASSIGNMENT', [p[1], p[3]])
        print 'p_assignment_expression_1'

    # Assignment Operator

    def p_assignment_operator(self, p):
        'assignment_operator : ASSIGNMENT'
        p[0] = p[1]
        print 'p_assignment_operator'

    # Proposition List
    def p_proposition_list_1(self, p):
        'proposition_list : proposition_implication_expression'
        p[0] = [p[1]]
        print 'p_proposition_list_1'

    '''def p_proposition_list_1(self, p):
        'proposition_list : proposition_list SEMICOLON \
                            proposition_implication_expression'
        p[0] = p[1].append(p[3])
        print 'p_proposition_list_1'''

    # Proposition Implication Expression

    def p_proposition_implication_expression_1(self, p):
        'proposition_implication_expression : \
             proposition_disjunction_expression'
        p[0] = p[1]
        print 'p_proposition_implication_expression_1'

    def p_proposition_implication_expression_2(self, p):
        'proposition_implication_expression : \
            proposition_implication_expression \
            IMPLICATION \
            proposition_disjunction_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'IMPLICATION',
                                [p[1], p[3]])
        print 'p_proposition_implication_expression_2'

    # Proposition Disjuction Expression

    def p_proposition_disjunction_expression_1(self, p):
        'proposition_disjunction_expression : proposition_conjunction_expression'
        p[0] = p[1]
        print 'p_proposition_disjunction_expression_1'

    def p_proposition_disjuction_expression_2(self, p):
        'proposition_disjunction_expression : \
            proposition_disjunction_expression \
            DISJUNCTION \
            proposition_conjunction_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'DISJUNCTION',
                                [p[1], p[3]])
        print 'p_proposition_disjunction_expression_2'

    # Proposition Conjunction Expression

    def p_proposition_conjunction_expression_1(self, p):
        'proposition_conjunction_expression : proposition_not_expression'
        p[0] = p[1]
        print 'p_proposition_disjunction_expression_1'

    def p_proposition_conjunction_expression_2(self, p):
        'proposition_conjunction_expression : \
            proposition_conjunction_expression \
            CONJUNCTION \
            proposition_not_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'CONJUNCTION',
                                [p[1], p[3]])
        print 'p_proposition_disjunction_expression_2'

    # Proposition Not Expression

    def p_proposition_not_expression_1(self, p):
        'proposition_not_expression : proposition_equality_expression'
        p[0] = p[1]
        print 'p_proposition_not_expression_1'

    def p_proposition_not_expression_2(self, p):
        'proposition_not_expression : NOT proposition_not_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'NOT', [p[2]])
        print 'p_proposition_not_expression_2'

    # Proposition Equality Expression

    def p_proposition_equality_expression_1(self, p):
        'proposition_equality_expression : proposition_relational_expression'
        p[0] = p[1]
        print 'p_proposition_equality_expression_1'

    def p_proposition_equality_expression_2(self, p):
        'proposition_equality_expression : \
            proposition_equality_expression \
            EQUAL \
            proposition_relational_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'EQUAL',
                                [p[1],p[3]])
        print 'p_proposition_equality_expression_2'

    def p_proposition_equality_expression_3(self, p):
        'proposition_equality_expression : \
            proposition_equality_expression \
            NOTEQUAL \
            proposition_relational_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'NOTEQUAL',
                                [p[1],p[3]])
        print 'p_proposition_equality_expression_3'

    # Proposition Relation Expression

    def p_proposition_relational_expression_1(self, p):
        'proposition_relational_expression : item_expression'
        p[0] = p[1]
        print 'p_proposition_relational_expression_1'

    def p_proposition_relational_expression_2(self, p):
        'proposition_relational_expression : set_relational_expression'
        p[0] = p[1]
        print 'p_proposition_relational_expression_2'

    def p_proposition_relational_expression_3(self, p):
        'proposition_relational_expression : item_set_relational_expression'
        p[0] = p[1]
        print 'p_proposition_relational_expression_3'

    '''def p_proposition_relational_expression_4(self, p):
        'proposition_relational_expression : math_relational_expression'
        print 'p_proposition_relational_expression_4'''

    # Set Relational Expression (is a proposition)

    def p_set_relational_expression_1(self, p):
        'set_relational_expression : set_expression LESS set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'LESS',
                                [p[1],p[3]])
        print 'p_set_relational_expression_1'

    def p_set_relational_expression_2(self, p):
        'set_relational_expression : set_expression LESSEQUAL set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'LESSEQUAL',
                                [p[1],p[3]])
        print 'p_set_relational_expression_2'

    def p_set_relational_expression_3(self, p):
        'set_relational_expression : set_expression GREATEREQUAL set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'GREATEREQUAL',
                                [p[1],p[3]])
        print 'p_set_relational_expression_3'

    def p_set_relational_expression_4(self, p):
        'set_relational_expression : set_expression GREATER set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'GREATER',
                                [p[1],p[3]])
        print 'p_set_relational_expression_4'

    # Item Set Relational Expression (is a proposition)

    def p_item_set_relational_expression_1(self, p):
        'item_set_relational_expression : \
             item_expression \
             BELONGTO \
             set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'BELONGTO',
                                [p[1],p[3]])
        print 'p_item_set_relational_expression_1'

    def p_item_set_relational_expression_2(self, p):
        'item_set_relational_expression : \
             item_expression \
             NOTBELONGTO \
             set_expression'
        p[0] = Proposition_Node('PROPOSITION', None, 'NOTBELONGTO',
                                [p[1],p[3]])
        print 'p_item_set_relational_expression_2'

    # Math Relational Expression

    '''def p_math_relational_expression_1(self, p):
        'math_relational_expression : math_expression LESS math_expression'
        print 'p_math_relational_expression_1'

    def p_math_relational_expression_2(self, p):
        'math_relational_expression : math_expression LESSEQUAL math_expression'
        print 'p_math_relational_expression_2'

    def p_math_relational_expression_3(self, p):
        'math_relational_expression : \
             math_expression \
             GREATEREQUAL \
             math_expression'
        print 'p_math_relational_expression_3'

    def p_math_relational_expression_4(self, p):
        'math_relational_expression : math_expression GREATER math_expression'
        print 'p_math_relational_expression_4'''

    # Item Expression tuple > math > set > proposition

    def p_item_expression(self, p):
        'item_expression : set_expression'
        #                   | tuple_expression
        #                   | math_expression
        #'
        p[0] = p[1]
        print 'p_item_expression'
        
    # Set Expression

    def p_set_expression_1(self, p):
        'set_expression : set_difference_expression'
        p[0] = p[1]
        print 'p_set_expression_1'

    # Set Difference Expression

    def p_set_difference_expression_1(self, p):
        'set_difference_expression : set_union_expression'
        p[0] = p[1]
        print 'p_set_difference_expression_1'

    def p_set_difference_expression_2(self, p):
        'set_difference_expression : \
             set_difference_expression \
             DIFFERENCE \
             set_union_expression'
        p[0] = Set_Node('SET', None, 'DIFFERENCE', False,
                        [p[1], p[3]])
        print 'p_set_difference_expression_2'

    # Set Union Expression

    def p_set_union_expression_1(self, p):
        'set_union_expression : set_intersection_expression'
        p[0] = p[1]
        print 'p_set_union_expression_1'

    def p_set_union_expression_2(self, p):
        'set_union_expression : \
            set_union_expression \
            UNION \
            set_intersection_expression'
        p[0] = Set_Node('SET', None, 'UNION', False,
                        [p[1], p[3]])
        print 'p_set_union_expression_2'

    # Set Intersection Expression

    def p_set_intersection_expression_1(self, p):
        'set_intersection_expression : set_item_expression'
        p[0] = p[1]
        print 'p_set_intersection_expression_1'

    def p_set_intersection_expression_2(self, p):
        'set_intersection_expression : \
            set_intersection_expression \
            INTERSECTION \
            set_item_expression'
        p[0] = Set_Node('SET', None, 'INTERSECTION', False,
                        [p[1], p[3]])
        print 'p_set_intersection_expression_2'

    # Set Item Expression List
    def p_set_item_expression_list_1(self, p):
        'set_item_expression_list : math_expression'
        p[0] = [p[1]]
        print 'p_set_item_expression_list_1'

    def p_set_item_expression_list_2(self, p):
        'set_item_expression_list : set_item_expression_list \
                                    COMMA \
                                    math_expression'
        p[0] = p[1] + [p[3]]
        print 'p_set_item_expression_list_2'

    # Set Item Expression

    def p_set_item_expression_1(self, p):
        'set_item_expression : math_expression'
        p[0] = p[1]
        print 'p_set_item_expression_1'

    '''def p_set_item_expression_2(self, p):
        'set_item_expression : LBRACE math_expression RBRACE'
        p[0] = Set_Node('SET', None, None, True, [p[2]])
        print 'p_set_item_expression_2'''

    def p_set_item_expression_2(self, p):
        'set_item_expression : LBRACE \
                                 set_item_expression_list \
                                 RBRACE'
        p[0] = Set_Node('SET', None, None, True, p[2])
        print 'p_set_item_expression_3'

    def p_set_item_expression_3(self, p):
        'set_item_expression : LBRACE \
                                 lprimary_expression \
                                 SEPERATOR \
                                 proposition_implication_expression \
                                 RBRACE'
        p[0] = Set_Node('SET', None, None, False, [p[2], p[4]])
        print 'p_set_item_expression_4'

    # Math Expression

    def p_math_expression(self, p):
        'math_expression : math_additive_expression'
        p[0] = p[1]
        print 'p_math_expression'

    # Math Additive Expression

    def p_math_additive_expression_1(self, p):
        'math_additive_expression : math_multiplicative_expression'
        p[0] = p[1]
        print 'p_math_additive_expression_1'

    def p_math_additive_expression_2(self, p):
        'math_additive_expression : \
            math_additive_expression \
            PLUS \
            math_multiplicative_expression'
        p[0] = Math_Node('MATH', p[3].value_type, 'PLUS', [p[1], p[3]])
        print 'p_math_additive_expression_2'

    def p_math_additive_expression_3(self, p):
        'math_additive_expression : \
            math_additive_expression \
            MINUS \
            math_multiplicative_expression'
        p[0] = Math_Node('MATH', p[3].value_type, 'MINUS', [p[1], p[3]])
        print 'p_math_additive_expression_3'

    # Math Multiplication ExpBRACEression

    def p_math_multiplication_expression_1(self, p):
        'math_multiplicative_expression : cast_expression'
        p[0] = p[1]
        print 'p_math_multiplication_expression_1'

    def p_math_multiplicative_expression_2(self, p):
        'math_multiplicative_expression : \
            math_multiplicative_expression \
            TIMES \
            cast_expression'
        p[0] = Math_Node('MATH', p[3].value_type, 'TIMES', [p[1], p[3]])
        print 'p_math_multiplication_expression_2'

    def p_math_multiplicative_expression_3(self, p):
        'math_multiplicative_expression : \
            math_multiplicative_expression \
            DIVIDE \
            cast_expression'
        p[0] = Math_Node('MATH', p[3].value_type, 'DIVIDE', [p[1], p[3]])
        print 'p_math_multiplication_expression_3'

    def p_math_multiplicative_expression_4(self, p):
        'math_multiplicative_expression : \
            math_multiplicative_expression \
            MOD \
            cast_expression'
        p[0] = Math_Node('MATH', p[3].value_type, 'MOD', [p[1], p[3]])
        print 'p_math_multiplication_expression_4'

    # Cast Expression

    def p_cast_expression_1(self, p):
        'cast_expression : unary_expression'
        p[0] = p[1]
        print 'p_cast_expression_1'

    def p_cast_expression_2(self, p):
        'cast_expression : LPAREN type_specifier RPAREN cast_expression'
        p[0] = Node('CAST', None, None, [p[2], p[4]])
        #p[0].value = p[2].value # Maybe wrong, need test.
        print 'p_cast_expression_2'

    # Unary Expression

    def p_unary_expression_1(self, p):
        'unary_expression : postfix_expression'
        p[0] = p[1]
        print 'p_unary_expression_1'

    def p_unary_expression_2(self, p):
        'unary_expression : unary_operator cast_expression'
        if p[1] == '*':
            # ID, Value, Address
            p[0] = Node('POINTER', p[2].value_type, None, [p[2], None, None])
        elif p[2].value_type in ('NUMBER', 'RNUMBER', 'CHAR'):
            if p[1] == '+':    # PLUS
                p[0] = p[2]
            else:
                p[0] = Math_Node('MATH', p[2].value_type, 'MINUS',
                    [Math_Node('MATH', p[2].value_type, None, [0]), p[2]])
        
        print 'p_unary_expression_2'

    # Unary Operator

    def p_unary_operator(self, p):
        '''unary_operator : PLUS
                          | MINUS
                          | TIMES'''
        p[0] = p[1]
        print 'p_unary_operator'

    # Postfix Expression

    def p_postfix_expression_1(self, p):
        'postfix_expression : primary_expression'
        p[0] = p[1]
        print 'p_postfix_expression_1'

    # This is an array t[x]
    def p_postfix_expression_2(self, p):
        'postfix_expression : postfix_expression \
                             LBRACKET math_expression RBRACKET'
        if p[1].symbol_type == 'ID' and p[1].value_type == 'TUPLE':
            p[0] = Node(symbol_type = 'ARRAY',value = [p[1], p[3]])
        print 'p_postfix_expression_2'

    def p_postfix_expression_3(self, p):
        'postfix_expression : postfix_expression LPAREN RPAREN'
        if p[1].symbol_type == 'ID':
            p[0] = Node(symbol_type = 'FUNC',value = [p[1], None])
        print 'p_postfix_expression_3'

    def p_postfix_expression_4(self, p):
        'postfix_expression : \
            postfix_expression \
            LPAREN \
            argument_expression_list \
            RPAREN'
        if p[1].symbol_type == 'ID':
            p[0] = Node(symbol_type = 'FUNC',value = [p[1], p[3]])
        print 'p_postfix_expression_4'

    # Primary Expression

    def p_primary_expression_1(self, p):
        '''
        primary_expression : lprimary_expression
                           | constant
                           | STRING
                           | NIL
        '''
        p[0] = p[1]
        print 'p_primary_expression'

    def p_primary_expression_2(self, p):
        'primary_expression : LPAREN proposition_implication_expression RPAREN'
        p[0] = p[2]
        print 'p_primary_expression_2'

    #def p_lprimary_expression(self, p):

    def p_lprimary_expression(self, p):
        '''lprimary_expression : ID
                               | tuple_expression
                               | ID DOT LESS ID BELONGTO ID GREATER
                               | ID DOT LESS ID GREATER
                               | ID DOT LESS ID BELONGTO TIMES ID GREATER'''
        if isinstance(p[1],basestring):
            if len(p) == 2:
                p[0] = Node('ID', None, None, [p[1], None])
            elif len(p) == 6:
                p[0] = Node('STRUCT', None, None, [p[1], p[4]])
            elif len(p) == 8:
                p[0] = Node('STRUCT', None, None, [p[1], p[4], p[6]])
            else: # len(p) == 9
                p[0] = Node('STRUCT_POINTER', None, None, [p[1], p[4], p[7]])
        else:
            p[0] = p[1]
        print 'p_lprimary_expression'

    # Argument Expression List

    def p_argument_expression_list_1(self, p):
        'argument_expression_list : assignment_expression'
        p[0] = [p[1]]
        print 'p_argument_expression_list_1'

    def p_argument_expression_list_2(self, p):
        'argument_expression_list : \
            argument_expression_list COMMA assignment_expression'
        p[0] = p[1] + [p[3]]
        print 'p_argument_expression_list_2'

    # Constant

    def p_constant_1(self, p):
        'constant : NUMBER'
        p[0] = Math_Node('CONST', 'NUMBER', None, p[1])
        print 'p_constant_1'

    def p_constant_2(self, p):
        'constant : RNUMBER'
        p[0] = Math_Node('CONST', 'RNUMBER', None, p[1])
        print 'p_constant_2'

    def p_constant_3(self, p):
        'constant : CHAR'
        p[0] = Math_Node('CONST', 'CHAR', None, p[1])
        print 'p_constant_3'

    # proposition_implication_expression_list

    def p_set_expression_list_1(self, p):
        'set_expression_list : set_expression'
        p[0] = [p[1]]
        print 'p_set_expression_list_1'

    def p_set_expression_list_2(self, p):
        'set_expression_list : set_expression_list COMMA set_expression'
        p[0] = p[1] + [p[3]]
        print 'p_set_expression_list_2'

    # Tuple expression

    def p_tuple_expression_1(self, p):
        'tuple_expression : LESS set_expression_list GREATER'
        p[0] = Tuple_Node(symbol_type = 'TUPLE', value = p[2])
        print 'p_tuple_expression_1'

    '''def p_tuple_expression_2(self, p):
        'tuple_expression : LESS \
                           tuple_expression \
                           COMMA \
                           proposition_implication_expression \
                           FORALL'
        print 'p_tuple_expression_2'
    '''

    # Error

    def p_error(self, p):
        if p:
            print("\nSyntax error at line %d '%s'\n" %(p.lineno, p.value))
        else:
            print("\nSyntax error at EOF\n")

    #start = 'set_relational_expression'#'tuple_expression'

if __name__ == '__main__':
    '''
MACHINE TEST(type t)
ATTRIBUTES
    type T_VMK_ReturnCode, T_UBYTE, T_UWORD;
    

OPERATIONS
T_VMK_ReturnCode vmkGetVMID(
    T_UBYTE ubpName,
    T_UWORD uwpVMID
){
if(ubpName==NULL){
	uwpVMID=curVMID;
	return VMK_OK;
}
if(NoValidName(ubpName)){
	return VMK_INVALID_ADDRESS;
}
if(vm.<NAME:ubpName>:appVM){
	return VMK_INVALID_NAME;
}
uwpVMID=vm.<ID>;
return VMK_OK;
}
END
'''
    '''
ATTRIBUTES
    int *x;
    

OPERATIONS
T_VMK_ReturnCode vmkGetVMID(){
*x = 1;
return *x;
}
'''
    f = open('test.txt', 'r')
    m = Proof_Parser()
    #x = m.run(''.join(f.readlines()))
    f.close()
    x = m.run('''
MACHINE TEST(type t)

ATTRIBUTES
	type T_UBYTE, T_UWORD, T_VMK_ReturnCode;
	T_VMK_ReturnCode VMK_OK, VMK_INVALID_ADDRESS, VMK_INVALID_NAME;


OPERATIONS
T_VMK_ReturnCode vmkSyscallGetVMID(
	T_UBYTE *name,
	T_UWORD *vmID
){
if(~checkValidAddress(vmID)){
	return VMD_INVALID_ADDRESS;
}
if(*name==NULL){
	*vmID=curVM.<ID>;
	return VMK_OK;
}
if(~checkValidAddress(name)){
	return VMD_INVALID_ADDRESS;
}
vm.<NAME:*name>:appVM;
if(vm==NULL){
	return VMK_INVALID_NAME;
}
*vmID=vm.<ID>;
return VMK_OK;
}
END
''')

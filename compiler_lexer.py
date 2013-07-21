# -----------------------------------------------------------------------------
# compiler_lexer.py
#
# Author: Angel
# Created Date: 2013-04-10
# Last Changed: 2013-04-10
# -----------------------------------------------------------------------------

import ply.lex as lex

class Lexer:
    # Reserved words.
    reserved = {
        'MACHINE'    : 'MACHINE',
        'INVARIANT'  : 'INVARIANT',
        'ATTRIBUTES' : 'ATTRIBUTES',
        'OPERATIONS' : 'OPERATIONS',
        'END'        : 'END',
        'const'      : 'CONST',
        'int'        : 'TYPE_INT',
        'float'      : 'TYPE_FLOAT',
        'char'       : 'TYPE_CHAR',
        'string'     : 'TYPE_STRING',
        'bool'       : 'TYPE_BOOL',
        'proposition': 'TYPE_PROPOSITION',
        'set'        : 'TYPE_SET',
        'tuple'      : 'TYPE_TUPLE',
        'NULL'        : 'NIL',
        'true'       : 'TRUE',
        'false'      : 'FALSE',
        'void'       : 'VOID',
        'return'     : 'RETURN',
        'if'         : 'IF',
        'else'       : 'ELSE',
        'while'      : 'WHILE',
        'type'       : 'TYPE'
        }

    # List of token names.   This is always required
    tokens = [
        'ID',              # identifier
        'NUMBER',          # integer
        'RNUMBER',         # real number
        'CHAR',            # char
        'STRING',          # string
        # EXPRESSION
        # PROPOSITION
        # SET
        # TUPLE
        # MATH
        # ARRAY
        # FUNC               funcall
        # FUN                function
        # FUNDEF
        # MACHINE
        # CAST               force transform
        # STRUCT             e.g. vm.<ID>
        'PLUS',            # +
        'MINUS',           # -
        'TIMES',           # *
        'DIVIDE',          # /
        'MOD',             # %
        'NOT',             # ~
        'CONJUNCTION',     # /\
        'DISJUNCTION',     # \/
        'IMPLICATION',     # ->
        'FORALL',          # #
        'EXIST',           # !
        'LESS',            # <
        'LESSEQUAL',       # <=
        'EQUAL',           # ==
        'GREATEREQUAL',    # >=
        'GREATER',         # >
        'NOTEQUAL',        # !=
        'SEPERATOR',       # |
        'BELONGTO',        # :
        'NOTBELONGTO',     # !:
        'INTERSECTION',    # /-\
        'UNION',           # \-/
        'DIFFERENCE',      # --
        'ASSIGNMENT',      # =
        'LPAREN',          # (
        'RPAREN',          # )
        'LBRACKET',        # [
        'RBRACKET',        # ]
        'LBRACE',          # {
        'RBRACE',          # }
        'COMMA',           # ,
        'SEMICOLON',       # ;
        'DOT',             # .
        ] + list(reserved.values())

    # Regular expression rules for simple tokens
    t_PLUS         = r'\+'
    t_MINUS        = r'-'
    t_TIMES        = r'\*'
    t_DIVIDE       = r'/'
    t_NOT          = r'~'
    t_MOD          = r'%'
    t_CONJUNCTION  = r'/\\'
    t_DISJUNCTION  = r'\\/'
    t_IMPLICATION  = r'->'
    t_LESS         = r'<'
    t_LESSEQUAL    = r'<='
    t_EQUAL        = r'=='
    t_GREATEREQUAL = r'>='
    t_GREATER      = r'>'
    t_NOTEQUAL     = r'!='
    t_SEPERATOR    = r'\|'
    t_BELONGTO     = r':'
    t_NOTBELONGTO  = r'!:'
    t_INTERSECTION = r'/-\\'
    t_UNION        = r'\\-/'
    t_DIFFERENCE   = r'--'
    t_ASSIGNMENT   = r'='
    t_LPAREN       = r'\('
    t_RPAREN       = r'\)'
    t_LBRACKET     = r'\['
    t_RBRACKET     = r'\]'
    t_LBRACE       = r'\{'
    t_RBRACE       = r'\}'
    t_COMMA        = r'\,'
    t_SEMICOLON    = r';'
    t_DOT          = r'\.'

    # Maybe not in use.
    t_FORALL       = r'\#'
    t_EXIST        = r'!'

    # A regular expression rule with some action code
    # Note addition of self parameter since we're in a class
    def t_RNUMBER(self, t):
        r'\d+\.\d+'
        t.value = float(t.value)
        return t

    def t_CHAR(self, t):
        r'\'.\''    # How about escape characters?
        t.value = t.value[1: -1]
        return t

    def t_STRING(self, t):
        r'".+"'
        t.value = t.value[1: -1]
    
    def t_NUMBER(self,t):
        r'\d+'
        try:
            t.value = int(t.value)
        except ValueError:
            print "Integer value too large %s" %t.value
            t.value = 0
        return t

    def t_ID(self, t):
        r'[_A-Za-z][\w_]*'
        t.type = Lexer.reserved.get(t.value, 'ID')
        return t

    # Define a rule so we can track line numbers
    def t_newline(self,t):
        r'\n+'
        t.lexer.lineno += t.value.count('\n')

    # A string containing ignored characters (spaces and tabs)
    t_ignore  = ' \t'

    # Error handling rule
    def t_error(self,t):
        print "\nIllegal character '%s'\n" % t.value[0]
        t.lexer.skip(1)

    # Build the lexer
    def build(self,**kwargs):
        self.lexer = lex.lex(module=self, **kwargs)
    
    # Test it output
    def test(self,data):
        self.lexer.input(data)
        while True:
             tok = self.lexer.token()
             if not tok: break
             print tok

m = Lexer()
#m.build()
#lexer = m.lexer

if __name__ == '__main__':
    f = open('test.txt', 'r')
    m.build()
    #m.test(''.join(f.readlines()))
    f.close()
    m.test('''
MACHINE TEST(type t)
OPERATIONS
T_VMK_ReturnCode vmkGetVMID(){
uwpVMID = vm.<ID>;
}
END
''')
    

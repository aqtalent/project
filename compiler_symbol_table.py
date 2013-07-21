class Symbol_Table(object):
    def __init__(self, name = None, invariant_list = [], table = {}, upper_table = None):
        self.name = name
        self.table = table
        self.invariant_list = invariant_list
        self.upper_table = upper_table

sb = []

class Node(object):
    '''
        symbol_type: proposition/set/tuple/math_expression/id
        value_type: expression/number/rnumber/char/string/bool
        operation: +|-|*|/...
        value: a list of child nodes
        parent: the tree parent of this node
    '''
    def __init__(self,
                 symbol_type = None,
                 value_type= None,
                 operation = None,
                 value = None
                 ):
        self.symbol_type = symbol_type
        self.value_type = value_type
        self.operation = operation
        self.value = value
        self.parent = None

        self.set_children_parent()

    def set_children_parent(self):
        if isinstance(self.value, list):
            for item in self.value:
                if isinstance(item, Node):
                    item.parent = self
        elif isinstance(self.value, Node):
            self.value.parent = self

'''class Symbol_Table(object):
    def __init__(self):
        self.symbol_table = {}

    def get_symbol(self, key):
        if self.symbol_table.has_key(key):
            return self.symbol_table[key]
        else:
            return None

    def add_symbol(self, symbol):
        if self.get_symbol(symbol.vale) == None:
            self.symbol_table[symbol.value] = symbol
        # else:
            # error'''
    

        
class Statement_Node(Node):
    '''
        ASSIGNMENT
        FUNCALL
        SELECTION
        ITERATION
        JUMP
        EXPRESSION
        STATEMENTLIST
    '''
    def __init__(self,
                 symbol_type = 'EXPRESSION',
                 value_type = None,
                 operation = None,
                 value = None):
        super(Statement_Node, self).__init__(symbol_type,
                                            value_type,
                                            operation,
                                            value)

class Proposition_Node(Node):
    def __init__(self,
                 symbol_type = None,
                 value_type= None,
                 operation = None,
                 value = None
                 ):
        super(Proposition_Node, self).__init__(symbol_type,
                                               value_type,
                                               operation,
                                               value)
        #self.value = value

class Set_Node(Node):
    def __init__(self,
                 symbol_type = None,
                 value_type= None,
                 operation = None, # operation == None means a atom set
                                   # no /-\ or \-/ included
                 if_exhaustivity = True, # {1, 2, 3} or {x| x > 0 /\ x < 4}
                 value = None,
                 #in_type = None
                 ):
        super(Set_Node, self).__init__(symbol_type,
                                       value_type,
                                       operation,
                                       value)
        
        #self.value = value
        self.if_exhaustivity = if_exhaustivity
        #self.in_type = in_type

class Tuple_Node(Node):
    def __init__(self,
                 symbol_type = None,
                 value_type= None,
                 operation = None, 
                 value = None,
                 #in_type = None
                 ):
        super(Tuple_Node, self).__init__(symbol_type,
                                         value_type,
                                         operation,
                                         value)
        #self.value = value
        self.len = len(value)
        #self.in_type = in_type

class Math_Node(Node):
    def __init__(self,
                 symbol_type = None,
                 value_type= None,
                 operation = None, # None means literals
                 value = None
                 ):
        super(Math_Node, self).__init__(symbol_type,
                                        value_type,
                                        operation,
                                        value)
        #self.value = value

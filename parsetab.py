
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.2'

_lr_method = 'LALR'

_lr_signature = "\xc0\xc3\x9f\x13:\x93\x19\x9c\xc6\xa6@'\x85\x96H\xbb"
    
_lr_action_items = {'PLUS':([1,],[3,]),'NUMBER':([0,3,],[1,4,]),'$end':([2,4,],[0,-1,]),}

_lr_action = { }
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = { }
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'exp':([0,],[2,]),}

_lr_goto = { }
for _k, _v in _lr_goto_items.items():
   for _x,_y in zip(_v[0],_v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = { }
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> exp","S'",1,None,None,None),
  ('exp -> NUMBER PLUS NUMBER','exp',3,'p_exp','E:\\cloud189\\\xb1\xcf\xc9\xe8\\Build a proof checker by myself\\project\\compiler_parser.py',5),
]

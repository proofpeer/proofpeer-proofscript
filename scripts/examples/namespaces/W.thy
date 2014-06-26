theory examples\W 
  n = namespaces
  U = n\U
  V = n\V
extends U V

failure x
assert U\x == n\U\x == \examples\namespaces\U\x == 
  namespaces\U\x == "U"
assert V\x == n\V\x == \examples\namespaces\V\x == 
  namespaces\V\x == "V"



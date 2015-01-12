theory W 
  n = \examples\namespaces\uv
  U = n\U
  V = n\V
extends U V

failure x
assert U\x == n\U\x == \examples\namespaces\uv\U\x == 
  uv\U\x == "U"
assert V\x == n\V\x == \examples\namespaces\uv\V\x == 
  uv\V\x == "V"



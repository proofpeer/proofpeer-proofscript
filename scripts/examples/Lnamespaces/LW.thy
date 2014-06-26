theory examples\LW 
  n = namespaces
  U = n\LU
  V = n\LV
extends U V

failure 'x'
assert 'U\x' == 'n\LU\x' == '\examples\namespaces\LU\x' == 
  'namespaces\LU\x'
assert 'V\x' == 'n\LV\x' == '\examples\namespaces\LV\x' == 
  'namespaces\LV\x' 



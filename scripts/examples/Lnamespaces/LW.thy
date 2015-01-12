theory LW 
  n = \examples\Lnamespaces\uv
  U = n\LU
  V = n\LV
extends U V

failure 'x'
assert 'U\x' == 'n\LU\x' == '\examples\Lnamespaces\uv\LU\x' == 
  'uv\LU\x'
assert 'V\x' == 'n\LV\x' == '\examples\Lnamespaces\uv\LV\x' == 
  'uv\LV\x' 



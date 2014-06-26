theory \LE 
extends \LC \LD

assert 'x' == '\LB\x'
failure 'y'
failure 'z'

let 'y = \LC\y'
let 'z = \LD\z'

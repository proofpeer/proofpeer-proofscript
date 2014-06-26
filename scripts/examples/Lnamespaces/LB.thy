theory \LB extends \LA

assert 'x' == '\LA\x' and 'y' == '\LA\y' and 'z' == '\LA\z' 

let 'x'

assert '\LA\x' <> 'x' == '\LB\x'
 

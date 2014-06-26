theory \LA extends \root

let 'x'
let 'y'
let 'z'

assert 'x' == '\LA\x'

# this is just an arbitrary test of how invalid namespaces within terms are handled:
failure '\A\x'

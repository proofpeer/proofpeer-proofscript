theory \LC extends \LB

assert 'x' == '\LB\x' and 'y' == '\LB\y' == '\LA\y' and 'z' == '\LB\z' == '\LA\z'

let 'y'
let 'z'

assert 'y' == '\LC\y' <> '\LB\y' and 'z' == '\LC\z' <> '\LB\z'


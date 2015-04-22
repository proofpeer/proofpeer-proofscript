theory issue56 extends \root

def trivial t = tm => t

context
  let 'p : ℙ'
  assume p: 'p'
  theorem 'p' by trivial 
    p
  theorem 'p' by (trivial p)
  theorem 'p' by trivial p

context

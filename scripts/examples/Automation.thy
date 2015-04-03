theory Automation extends \root

context
  assume t: '∀ p. p → p'
  s : t 
  show s

failure theorem imp: '∀ p. p → p' .

failure theorem '∀ p. p → p' by nil

failure 
  
  theorem '1 + 2 = 3' by taut (term, parameter) -> theorem     
                         metis 
                         z3
                      by     

failure theorem '∀ q. q → q' by imp


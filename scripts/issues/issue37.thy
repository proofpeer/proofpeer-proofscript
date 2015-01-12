theory issue37 extends \root

assert "hello   
  world" == "hello\n  world"

val w = "hello     
      
    " 

assert w == "hello\n\n    "
assert size w == 11

assert "a b" <> "ab"

assert "  " <> ""
assert size "  " == 2

assert "a " <> "a"
assert size "a " == 2

assert "a " ++ " b" == "a  b"

theory \examples\Statements extends \root

# Examples for match

val wordOf = x => 
  match x
    case 0 => "none"
    case 1 => "one"
    case 2 => "two"
    case z if z > 0 => "many"

assert wordOf 0 == "none" and wordOf 1 == "one" and wordOf 2 == "two"
assert wordOf 5 == "many"
failure wordOf (-1)
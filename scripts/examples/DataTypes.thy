theory \examples\DataTypes extends \root

# This is the nil literal:
show nil

# These are the boolean literals:
show true
show false

# These are some integer literals:
show 42
show -1

# These are a few strings,
  some of them contain unicode characters specified
  by their codepoint:
show "Hello World"
show "symbol for universal type: \U0001D4B0"
show "symbol for type of propositions: \U00002119"
show "again, the symbol for the type of propositions: \u2119"
show "this namespace: \\examples\\DataTypes"
show "you can also have \n and \" in a string"

# This is a vector literal
show [1, 2, "hello", false]

# This is a vector literal denoting the same vector
show (1, 2, "hello", false)
assert (1, 2, "hello", false) == [1, 2, "hello", false]

# This is a single element vector containing 7
show [7] 

# and this is just the number 7, not a vector
show (7)

# This is a function literal
show x => x * x

# here we apply this function literal to 7
show (x => x * x) 7

# You can convert integers into strings 
assert string (2 - 5) == "-3" 

# This is a comparison chain, which is true if every single member of the chain is true
assert 1 < 3 < 5 < 7 < 7 * 7 == 49 < 50 <= 50 <= 100 > 99

# The order for strings is lexicographic 
assert "ac" < "b"

# But for vectors it is elementwise
assert not ["a", "c"] <= ["b"]
assert not ["a", "c"] >= ["b"]
assert ["a", "c"] < ["b", "d"]

# Comparisons between values of different types always yields false, except for
  inequality, which always yields true
assert not 1 <= "1"
assert not 1 < "1"
assert not 1 == "1"
assert 1 <> "1"
assert nil <> (x => x)

# Functions cannot be compared with each other
failure (x => x) == (x => x)
failure (x => x) <> (x => x)

# This demonstrates failure in a neat way
failure failure 1 == 1

# Both strings and vectors have a size
assert size "hello" == size ("h", "e", "l", "l", "o") == 5

# There are the usual operations on booleans
assert not false
assert false or true
assert not (false and true)

# And addition, multiplication, division and modulo for integers
assert 7 + 5 == 12 and 7 * 5 == 35 and 7 / 5 == 1 and 7 mod 5 == 2

# Both strings and vectors can be concatenated
assert "hel" ++ "lo" == "hello" and ["h", "e", "l"] ++ ["l", "o"] == ["h", "e", "l", "l", "o"]

# For vectors, you can prepend and append elements
assert "h" <+ ["e", "l", "l"] +> "o" == ["h", "e", "l", "l", "o"]

# You can create ranges of integers like that:
assert 2 to 6 == [2, 3, 4, 5, 6] 
assert 6 to 2 == []
assert 6 downto 2 == [6, 5, 4, 3, 2]
assert 2 downto 6 == []

# Selecting individual characters from a string works like that:
assert "hello" 0 == "h" and "hello" 1 == "e" and "hello" 2 == "l" and "hello" 4 == "o"
failure "hello" (-1) 
failure "hello" 5
assert "hello" (1 to 3) == "ell"

# Selecting individual elements from a vector works the same:
assert ["h", "e", "l", "l", "o"] (1 to 3) == ["e", "l", "l"]
assert ["h", "e", "l", "l", "o"] (0, 2, 4) == ["h", "l", "o"]
failure ["h", "e", "l", "l", "o"] (1 to 5)

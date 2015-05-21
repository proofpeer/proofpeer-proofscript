theory CustomDatatypes extends \root

datatype Option
  None
  Some x

datatype 
  List
    Nil
    Cons (head, tail : List)

datatype
  Day
    Day (day : Integer) if day >= 1 and day <= 31
  Month 
    Month (month : Integer) if month >= 1 and month <= 12
  Year
    Year (year : Integer)

def 
  isLeapYear (Year year) if year mod 400 == 0 = true
  isLeapYear (Year year) if year mod 100 == 0 = false
  isLeapYear (Year year) if year mod 4 == 0 = true
  isLeapYear (Year year) = false

def countDaysOfMonth (month : Month, leap : Boolean) = 
  match !month
    case 1 => 31
    case 2 => if leap then 29 else 28
    case 3 => 31
    case 4 => 30
    case 5 => 31
    case 6 => 30
    case 7 => 31
    case 8 => 31
    case 9 => 30
    case 10 => 31
    case 11 => 30
    case 12 => 31

do
  val days = 0
  val leapDays = 0
  for i in 1 to 12 do
    days = days + countDaysOfMonth (Month i, false)
    leapDays = leapDays + countDaysOfMonth (Month i, true)
  assert days == 365
  assert leapDays == 366

def isValidDate (day : Day, month : Month, year : Year) : Boolean = 
  !day <= countDaysOfMonth(month, isLeapYear year)
  
datatype Date
  Date dmy if isValidDate dmy

def mkDate (day : Integer, month : Integer, year : Integer) : Date =
  Date (Day day, Month month, Year year)

def destDate (date : Date) = 
  match !date
    case (day, month, year) => (!day, !month, !year)

def checkDate d = 
  val date = mkDate d
  show date
  destDate date == d

assert checkDate (20, 7, 1969)
failure mkDate (29, 2, 2015)
assert checkDate (28, 2, 2015)
assert mkDate (20, 7, 1969) == mkDate(20, 7, 1969)
assert mkDate (20, 7, 1969) <> mkDate(20, 8, 1969)
assert mkDate (20, 7, 1969) <> mkDate(21, 7, 1969)
assert mkDate (20, 7, 1969) <> mkDate(20, 7, 1970)

def 
  classify (_ : Month) = "month"
  classify (_ : Year) = "year"
  classify (_ : Day) = "day"
  classify (_ : Date) = "date"

assert classify (Year 2015) == "year"
failure classify 2015
assert classify (Month 10) == "month"
assert classify (Day 11) == "day"
assert classify (mkDate (20, 7, 1969)) == "date"
assert ((Day 10) : Day) == (Day 10)
failure ((Month 10) : Day) == (Day 10)

match Day 10
  case f x => 
    assert f == Day
    assert x == 10
  case _ =>

def 
  count f x = 1 + count x
  count (x, y) = count x + count y
  count _ = 0

assert count Nil == 0
assert count (Cons (1, Nil)) == 1
assert count (Cons (1, Cons(2, Nil))) == 2
assert Nil == Nil
assert Cons == Cons
assert Nil <> Cons
assert size {Nil, Cons} == 2
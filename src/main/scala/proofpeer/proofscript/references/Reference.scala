package proofpeer.proofscript.references

trait Attribute 
object Attribute {
  
  case class Location(city : String, state : Option[String], country : Option[String]) extends Attribute 
  def location(city : String) : Location = Location(city, None, None) 
  def location(city : String, country : String) : Location = Location(city, None, Some(country))

  // days and months start both with index 1
  case class Date(day : Option[Int], month : Option[Int], year : Int) extends Attribute
  def date(year : Int) : Date = Date(None, None, year)
  def date(month : Int, year : Int) : Date = Date(None, Some(month), year)
  def date(day : Int, month : Int, year : Int) : Date = Date(Some(day), Some(month), year)
  
  case class Publisher(name : String, location : Option[Location]) extends Attribute
  def publisher(name : String) : Publisher = Publisher(name, None)
  def publisher(name : String, location : Location) : Publisher = Publisher(name, Some(location))
  
  case class Pages(pages : Option[(Int, Int)], id : Option[Int]) extends Attribute
  def pages(fromPage : Int, toPage : Int) : Pages = Pages(Some(fromPage, toPage), None)
  
  case class Name(full : String, short : Option[String]) extends Attribute
  def name(full : String, short : String) : Name = Name(full, Some(short))
      
  case class Person(firstname : String, middlename : Option[String], lastname : String) extends Attribute
  def person(firstname : String, lastname : String) : Person = Person(firstname, None, lastname)
  
  case class Persons(persons : List[Person]) extends Attribute
  def persons(ps : Person*) : Persons = Persons(ps.toList)
  
  case class Title(title : String) extends Attribute
  def title(t : String) : Title = Title(t)
  
  case class DOI(doi : String) extends Attribute
  def doi(d : String) : DOI = DOI(d)
  
  case class Number(number : Int) extends Attribute
  
  case class URL(url : String) extends Attribute
  def url(u : String) : URL = URL(u)
  
}

abstract class Reference(val kind : Reference.EntryType, val attributes : Map[String, Attribute]) 
object Reference {
  trait EntryType
  object Misc extends EntryType
}

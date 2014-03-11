package proofpeer.proofscript.logic

private class KernelImpl(val mk_theorem : (Context, Term) => Theorem) extends Kernel {
  
  import Term._
  import Type._
  import Utils._
  
  sealed trait ContextKind 
  object ContextKind {
    case class Assume(thm_name : Name, assumption : Term) extends ContextKind
    case class Define(const_name : Name, thm_name : Name, tm : Term) extends ContextKind
    case class Introduce(const_name : Name, ty : Type) extends ContextKind
  }

  private class ContextImpl(val kind : ContextKind,
                            val namespace : String, 
                            val parentNamespaces : Set[String],
                            val parentContext : Option[ContextImpl],
                            val constants : Map[Name, (Type, Option[Name])],
                            val theorems : Map[Name, Term]) extends Context 
  {
    
    def kernel : Kernel = KernelImpl.this
        
    def typeOfTerm(term : Term) : Option[Type] = 
      KernelImpl.this.typeOfTerm(this, Map(), term)
    
    private def hasContextScope(name : Name) : Boolean = {
      name.namespace.isEmpty || name.namespace == Some(namespace)
    }
      
    private def contextOfName(name : Name) : ContextImpl = {
      if (hasContextScope(name)) this
      else {
        val namespace = name.namespace.get
        if (parentNamespaces.contains(namespace))
          contextOfNamespace(namespace).get.asInstanceOf[ContextImpl]
        else
          failwith("no such namespace found: " + namespace)
      }
    }
    
    def lookupConst(const_name : Name) : Option[(Type, Option[Name])] = {
      contextOfName(const_name).constants.get(const_name)
    }
    
    private def ensureContextScope(name : Name) {
      if (!hasContextScope(name)) 
        failwith("name "+name+" is outside of namespace: "+namespace)
    } 
    
    private def contains[T](name : Name, map : Map[Name, T]) : Boolean = {
      if (name.namespace.isDefined) 
        constants.contains(name)
      else {
        constants.contains(name) || constants.contains(Name(Some(namespace), name.name))
      }
    }

    def introduce(const_name : Name, ty : Type) : Context = {
      ensureContextScope(const_name)
      if (contains(const_name, constants))
        failwith("constant name "+const_name+" clashes with other constant in current scope")
      new ContextImpl(
          ContextKind.Introduce(const_name, ty),
          namespace,
          parentNamespaces,
          Some(this),
          constants + (const_name -> (ty, None)),
          theorems)
    }
    
    

    def assume(thm_name : Name, assumption : Term) : Theorem = null
  
    def define(const_name : Name, thm_name : Name, tm : Term) : Theorem = null
   
    def lookupTheorem(thm_name : Name) : Option[Theorem] = null
  
    def storeTheorem(thm_name : Name, thm : Theorem) : Context = null
    
    def lift(thm : Theorem) : Theorem = null
     
  }
  
  private var namespaces : Map[String, Context] = Map()
  
  def completedNamespaces = namespaces.keySet
  
  def contextOfNamespace(namespace : String) : Option[Context] = namespaces.get(namespace)
    
  def completeNamespace(context : Context) {
    if (!context.isInstanceOf[ContextImpl] || context.kernel != this) 
      failwith("context does not belong to this kernel")
    val namespace = context.namespace
    if (namespaces.contains(namespace)) failwith("this namespace has already been completed: "+namespace)
    // ToDo: Here we must check if the context does introduce or
    // define any constants with names that are not qualified by its namespace
    namespaces += (namespace -> context.asInstanceOf[ContextImpl])
  }
  
  def createNewNamespace(namespace : String, parents : Set[String]) : Context = {
    null
  }
      
  def typeOfTerm(c : Context, vars : Map[IndexedName, Type], term : Term) : Option[Type] = {
    term match {
      case PolyConst(name, alpha) =>
        name match {
          case Kernel.equals => Some(Fun(alpha, Fun(alpha, Prop)))
          case Kernel.forall | Kernel.exists => Some(Fun(Fun(alpha, Prop), Prop))
          case Kernel.choose => Some(Fun(Fun(alpha, Prop), alpha))            
          case _ => None
        }
      case Const(name) => c.typeOfConst(name)
      case Var(name) => vars.get(name)
      case Comb(f, x) => 
        (typeOfTerm(c, vars, f), typeOfTerm(c, vars, x)) match {
          case (Some(Fun(fdomain, frange)), Some(xty)) if fdomain == xty =>
            Some(frange)
          case _ => None
        }
      case Abs(name, ty, body) =>
        typeOfTerm(c, vars + (name -> ty), body) match {
          case Some(bodyty) => Some(Fun(ty, bodyty))
          case None => None            
        }
    }
  }
  
}


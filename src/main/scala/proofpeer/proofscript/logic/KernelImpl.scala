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
    case class Created(namespace : String, parentNamespaces : Set[String], ancestorNamespaces : Set[String]) extends ContextKind
    case class StoreTheorem(thm_name : Name, proposition : Term) extends ContextKind
    case object Complete extends ContextKind
  }

  private class ContextImpl(val kind : ContextKind,
                            val depth : Integer,
                            val created : ContextKind.Created,
                            val parentContext : Option[ContextImpl],
                            val constants : Map[Name, (Type, Option[Name])],
                            val theorems : Map[Name, Term]) extends Context 
  {
    
    def kernel : Kernel = KernelImpl.this
    
    def namespace = created.namespace
    
    def parentNamespaces = created.parentNamespaces
        
    def typeOfTerm(term : Term) : Option[Type] = 
      KernelImpl.this.typeOfTerm(this, Map(), term)
    
    private def hasContextScope(name : Name) : Boolean = {
      name.namespace.isEmpty || name.namespace == Some(namespace)
    }
      
    private def contextOfName(name : Name) : ContextImpl = {
      if (hasContextScope(name)) this
      else {
        val namespace = name.namespace.get
        if (created.ancestorNamespaces.contains(namespace))
          contextOfNamespace(namespace).get.asInstanceOf[ContextImpl]
        else
          failwith("no such namespace found: " + namespace)
      }
    }
    
    def lookupConstant(const_name : Name) : Option[(Type, Option[Name])] = {
      contextOfName(const_name).constants.get(const_name)
    }
    
    private def ensureContextScope(name : Name) {
      if (!hasContextScope(name)) 
        failwith("name "+name+" is outside of namespace: "+created.namespace)
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
        failwith("constant name " + const_name + " clashes with other constant in current scope")
      new ContextImpl(
          ContextKind.Introduce(const_name, ty),
          depth + 1,
          created,
          Some(this),
          constants + (const_name -> (ty, None)),
          theorems)
    } 

    def assume(thm_name : Name, assumption : Term) : Theorem = {
      ensureContextScope(thm_name)
      if (contains(thm_name, theorems))
        failwith("theorem name " + thm_name + " has already been defined")
      if (typeOfTerm(assumption) != Some(Prop))
        failwith("assumption is not a valid proposition")
      val context = 
        new ContextImpl(
            ContextKind.Assume(thm_name, assumption),
            depth + 1,
            created,
            Some(this),
            constants,
            theorems + (thm_name -> assumption))
      mk_theorem(context, assumption)
    }
  
    def define(const_name : Name, thm_name : Name, tm : Term) : Theorem = {
      ensureContextScope(const_name)
      ensureContextScope(thm_name)
      if (contains(const_name, constants))
        failwith("constant name "+const_name+" clashes with other constant in current scope")
      if (contains(thm_name, theorems))
        failwith("theorem name "+thm_name+" has already been defined")
      typeOfTerm(tm) match {
        case None =>
          failwith("the defining term is not a valid term")
        case Some(ty) =>
          val eq = Comb(Comb(PolyConst(Kernel.equals, ty), Const(const_name)), tm)
          val context = 
            new ContextImpl(
              ContextKind.Define(const_name, thm_name, tm),
              depth + 1,
              created,
              Some(this),
              constants + (const_name -> (ty, Some(thm_name))),
              theorems + (thm_name -> eq))
          mk_theorem(context, eq)         
      }
    }
   
    def lookupTheorem(thm_name : Name) : Option[Theorem] = {
      val context = contextOfName(thm_name)
      context.theorems.get(thm_name).map(mk_theorem(context, _))
    }
  
    def storeTheorem(thm_name : Name, thm : Theorem) : Context = {
      ensureContextScope(thm_name)
      if (contains(thm_name, theorems))
        failwith("theorem name "+thm_name+" has already been defined")
      if (KernelImpl.this != thm.context.kernel)   
        failwith("theorem belongs to a different kernel")
      if (thm.context != this)
        failwith("theorem belongs to a different context")
      new ContextImpl(
          ContextKind.StoreTheorem(thm_name, thm.proposition),
          depth + 1,
          created,
          Some(this),
          constants,
          theorems + (thm_name -> thm.proposition))
    }
    
    def lift(thm : Theorem) : Theorem = {
      null
    }
     
  }
  
  private var namespaces : Map[String, Context] = Map()
  
  def completedNamespaces = namespaces.keySet
  
  def contextOfNamespace(namespace : String) : Option[Context] = namespaces.get(namespace)
  
  private def isQualifiedName(name : Name) : Boolean = name.namespace.isDefined
  
  private def isQualifiedTerm(term : Term) : Boolean = {
    term match {
      case PolyConst(name, alpha) => isQualifiedName(name)
      case Const(name) => isQualifiedName(name)
      case Comb(f, x) => isQualifiedTerm(f) && isQualifiedTerm(x)
      case Abs(name, ty, body) => isQualifiedTerm(body)
      case Var(name) => true
    }
  }
  
  private def isQualifiedTheorem(thm_name : Name, proposition : Term) : Boolean = {
    isQualifiedName(thm_name) && isQualifiedTerm(proposition)
  }
    
  def completeNamespace(context : Context) : Context = {
    if (!context.isInstanceOf[ContextImpl] || context.kernel != this) 
      failwith("context does not belong to this kernel")
    val namespace = context.namespace
    if (namespaces.contains(namespace)) 
      failwith("this namespace has already been completed: "+namespace)
    val ctx = context.asInstanceOf[ContextImpl]
    val theorems = ctx.theorems.filter(th => isQualifiedTheorem(th._1, th._2))
    def isQualifiedConstant(key : Name, value : (Type, Option[Name])) : Boolean = {
      isQualifiedName(key) &&
      (value._2 match {
        case Some(thm_name) => theorems.contains(thm_name)
        case None => true
       })
    }
    val constants = ctx.constants.filter(c => isQualifiedConstant(c._1, c._2))   
    val completedContext = 
      new ContextImpl(
          ContextKind.Complete,
          ctx.depth + 1,
          ctx.created,
          Some(ctx),
          constants,
          theorems)  
    namespaces += (namespace -> completedContext)
    completedContext
  }
  
  def createNewNamespace(namespace : String, parents : Set[String]) : Context = {
    var ancestors : Set[String] = Set()
    if (contextOfNamespace(namespace).isDefined)
      failwith("namespace already exists: "+namespace)
    for (parent <- parents) {
      contextOfNamespace(parent) match {
        case Some(context) =>
          ancestors = ancestors ++ context.asInstanceOf[ContextImpl].created.ancestorNamespaces
          ancestors = ancestors + parent
        case None =>
          failwith("no such completed namespace: "+parent)
      }
    }
    val created = ContextKind.Created(namespace, parents, ancestors)
    new ContextImpl(
        created,
        0,
        created,
        None,
        Map(),
        Map())
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


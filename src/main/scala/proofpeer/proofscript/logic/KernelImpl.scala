package proofpeer.proofscript.logic

private class KernelImpl(val mk_theorem : (Context, Term) => Theorem) extends Kernel {
  
  import Term._
  import Type._
  import Utils._
  import KernelUtils._
  
  sealed trait ContextKind 
  object ContextKind {
    case class Assume(thm_name : Name, assumption : Term) extends ContextKind
    case class Define(const_name : Name, ty : Type, thm_name : Name, tm : Term) extends ContextKind
    case class Introduce(const_name : Name, ty : Type) extends ContextKind
    case class Created(namespace : String, parentNamespaces : Set[String], ancestorNamespaces : Set[String]) extends ContextKind
    case class StoreTheorem(thm_name : Name, proposition : Term) extends ContextKind
    case object Complete extends ContextKind
  }

  private class ContextImpl(val kind : ContextKind,
                            val depth : Integer,
                            val created : ContextKind.Created,
                            val parentContext : Option[ContextImpl],
                            val constants : Map[Name, Type],
                            val theorems : Map[Name, Term]) extends Context 
  {
    
    def kernel : Kernel = KernelImpl.this
    
    def namespace = created.namespace
    
    def parentNamespaces = created.parentNamespaces
        
    def typeOfTerm(term : Term) : Option[Type] = 
      KernelUtils.typeOfTerm(this, Map(), term)
    
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
    
    def typeOfConst(const_name : Name) : Option[Type] = {
      contextOfName(const_name).constants.get(const_name)
    }
    
    private def isComplete : Boolean = {
      kind match {
        case ContextKind.Complete => true
        case _ => false
      }
    }
    
    private def ensureContextScope(name : Name) {
      if (!hasContextScope(name)) 
        failwith("name "+name+" is outside of namespace: "+created.namespace)
    } 
    
    private def contains[T](name : Name, map : Map[Name, T]) : Boolean = {
      if (name.namespace.isDefined) 
        map.contains(name) || map.contains(Name(None, name.name))
      else 
        map.contains(name) || map.contains(Name(Some(namespace), name.name))
    }
    
    private def isPolyConst(name : Name) : Boolean = {
      val n = name.name
      (n == Kernel.equals.name || 
       n == Kernel.forall.name || 
       n == Kernel.exists.name || 
       n == Kernel.choose.name)
    }
    
    def introduce(const_name : Name, ty : Type) : Context = {
      if (isComplete) failwith("cannot extend completed context")
      ensureContextScope(const_name)
      if (contains(const_name, constants) || isPolyConst(const_name))
        failwith("constant name " + const_name + " clashes with other constant in current scope")
      new ContextImpl(
          ContextKind.Introduce(const_name, ty),
          depth + 1,
          created,
          Some(this),
          constants + (const_name -> ty),
          theorems)
    } 

    def assume(thm_name : Name, assumption : Term) : Theorem = {
      if (isComplete) failwith("cannot extend completed context")
      ensureContextScope(thm_name)
      if (contains(thm_name, theorems))
        failwith("theorem name " + thm_name + " has already been defined")
      if (typeOfTerm(assumption) != Some(Prop))
        failwith("assumption is not a valid proposition")
      if (isQualifiedName(thm_name) && !isQualifiedTerm(assumption))
        failwith("theorem name is qualified, but proposition contains unqualified constants")
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
      if (isComplete) failwith("cannot extend completed context")
      ensureContextScope(const_name)
      ensureContextScope(thm_name)
      if (contains(const_name, constants) || isPolyConst(const_name))
        failwith("constant name "+const_name+" clashes with other constant in current scope")
      if (contains(thm_name, theorems))
        failwith("theorem name "+thm_name+" has already been defined")
      if (isQualifiedName(thm_name) && !isQualifiedTerm(tm))
        failwith("theorem name is qualified, but proposition contains unqualified constants")
      typeOfTerm(tm) match {
        case None =>
          failwith("the defining term is not a valid term")
        case Some(ty) =>
          val eq = Comb(Comb(PolyConst(Kernel.equals, ty), Const(const_name)), tm)
          val context = 
            new ContextImpl(
              ContextKind.Define(const_name, ty, thm_name, tm),
              depth + 1,
              created,
              Some(this),
              constants + (const_name -> ty),
              theorems + (thm_name -> eq))
          mk_theorem(context, eq)         
      }
    }
   
    def lookupTheorem(thm_name : Name) : Option[Theorem] = {
      val context = contextOfName(thm_name)
      context.theorems.get(thm_name).map(mk_theorem(context, _))
    }
    
    def checkTheoremContext(thm : Theorem) {
      if (KernelImpl.this != thm.context.kernel)   
        failwith("theorem belongs to a different kernel")
      if (thm.context != this)
        failwith("theorem belongs to a different context")      
    }
  
    def storeTheorem(thm_name : Name, thm : Theorem) : Context = {
      ensureContextScope(thm_name)
      if (contains(thm_name, theorems))
        failwith("theorem name "+thm_name+" has already been defined")
      checkTheoremContext(thm)
      if (isQualifiedName(thm_name) && !isQualifiedTerm(thm.proposition))
        failwith("theorem name is qualified, but proposition contains unqualified constants")
      new ContextImpl(
          ContextKind.StoreTheorem(thm_name, thm.proposition),
          depth + 1,
          created,
          Some(this),
          constants,
          theorems + (thm_name -> thm.proposition))
    }
    
    def lift(thm : Theorem, preserve_structure : Boolean) : Theorem = {
      if (KernelImpl.this != thm.context.kernel)
        failwith("theorem belongs to a different kernel")
      val src_context = thm.context.asInstanceOf[ContextImpl]
      val src_namespace = src_context.namespace
      if (namespace != src_namespace) {
        if (created.ancestorNamespaces.contains(src_namespace)) {
          val prop = completedContext(src_namespace).liftLocally(thm, preserve_structure).proposition
          if (!isQualifiedTerm(prop))
            failwith("cannot lift theorem containing unqualified constants between namespaces")
          mk_theorem(this, prop)
        } else {
          failwith("cannot lift theorem from namespace '" + src_context.namespace +"' to namespace '"+namespace+"'")
        }
      } else {
        liftLocally(thm, preserve_structure)
      }
    }
    
    // Same as lift, but assumes that the theorem context has the same namespace as this context.
    private def liftLocally(thm : Theorem, preserve_structure : Boolean) : Theorem = {
      val src_context = thm.context.asInstanceOf[ContextImpl]
      val common_ancestor = findCommonAncestorContext(this, src_context)
      val lifted_thm = common_ancestor.liftLocallyUp(thm, preserve_structure)
      if (common_ancestor.depth == depth)
        lifted_thm
      else
        mk_theorem(this, lifted_thm.proposition)
    }
    
    private def liftLocallyUp(thm : Theorem, preserve_structure : Boolean) : Theorem = {
      import ContextKind._
      var context = thm.context.asInstanceOf[ContextImpl]
      var prop = thm.proposition      
      if (preserve_structure) {
        while (context.depth > depth) {
          context.kind match {
            case Assume(_, hyp) => 
              prop = mk_implies(hyp, prop)
            case Introduce(c, ty) => 
              prop = mk_forall(c, ty, prop)
            case Define(c, ty, _, _) =>
              prop = mk_exists(c, ty, prop)
            case _ => 
              // nothing to do, the context is non-logical
          }
          context = context.parentContext.get
        }
      } else {
        var consts : Set[Name] = collectConsts(prop)
        while (context.depth > depth) {
          context.kind match {
            case Assume(_, hyp) => 
              prop = mk_implies(hyp, prop)
              consts = collectConsts(hyp, consts)
            case Introduce(c, ty) => 
              if (consts.contains(c)) {
                prop = mk_forall(c, ty, prop)
                consts = consts - c
              }
            case Define(c, ty, _, _) =>
              if (consts.contains(c)) {
                prop = mk_exists(c, ty, prop)
                consts = consts - c
              }
            case _ => 
              // nothing to do, the context is non-logical
          }
          context = context.parentContext.get
        }        
      }
      mk_theorem(context, prop)
    }
    
    private def getTypeOfTerm(tm : Term) : Type = {
      typeOfTerm(tm) match {
        case None => failwith("term is not wellformed in this context")
        case Some(ty) => ty
      }
    }
  
    def reflexive(tm : Term) : Theorem = {
      val ty = getTypeOfTerm(tm)
      mk_theorem(this, mk_equals(ty, tm, tm))
    }
    
    def beta(a : Term) : Theorem = {
      val ty = getTypeOfTerm(a)
      val b = KernelUtils.beta(a)
      mk_theorem(this, mk_equals(ty, a, b))
    }

    def transitive(p : Theorem, q : Theorem) : Theorem = {
      checkTheoremContext(p)
      checkTheoremContext(q)
      val (a, b1, _) = dest_equals(p.proposition)
      val (b2, c, _) = dest_equals(q.proposition)
      if (alpha_equivalent(b1, b2))
        mk_theorem(this, mk_equals(Prop, a, c))
      else
        failwith("transitive: middle propositions are not alpha equivalent")
    }
    
  }
  
  private var namespaces : Map[String, Context] = Map()
  
  def completedNamespaces = namespaces.keySet
  
  def contextOfNamespace(namespace : String) : Option[Context] = namespaces.get(namespace)
  
  private def completedContext(namespace : String) : ContextImpl = {
    contextOfNamespace(namespace) match {
      case Some(c) => c.asInstanceOf[ContextImpl]
      case None => failwith("there is no completed namespace '" + namespace + "'")
    }
  }
          
  def completeNamespace(context : Context) : Context = {
    if (!context.isInstanceOf[ContextImpl] || context.kernel != this) 
      failwith("context does not belong to this kernel")
    val namespace = context.namespace
    if (namespaces.contains(namespace)) 
      failwith("this namespace has already been completed: "+namespace)
    val ctx = context.asInstanceOf[ContextImpl]
    val theorems = ctx.theorems.filterKeys(n => isQualifiedName(n))
    val constants = ctx.constants.filterKeys(n => isQualifiedName(n))   
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
        
  // This assumes that c1 and c2 belong to the same kernel and the same context
  private def findCommonAncestorContext(c1 : ContextImpl, c2 : ContextImpl) : ContextImpl = {
    var depth1 = c1.depth
    var context1 = c1
    var depth2 = c2.depth
    var context2 = c2
    var depth = if (depth1 > depth2) depth1 else depth2
    while (depth1 != depth2) {
      if (depth1 > depth2) {
        context1 = context1.parentContext.get
        depth1 = depth1 - 1
      } else {
        context2 = context2.parentContext.get
        depth2 = depth2 - 1
      }
    }
    if (context1 != context2) 
      failwith("no common ancestor context found")
    else 
      context1
  }
  
    
}


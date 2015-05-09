package proofpeer.proofscript.logic

private class KernelImpl(
  val mk_theorem_helper : (Context, Term) => Theorem,
  val mk_cterm : (Context, Term, Type) => CTerm) extends Kernel {
  
  import Term._
  import Type._
  import Utils._
  import KernelUtils._
  
  private def mk_theorem(context : Context, term : Term) : Theorem = {
    mk_theorem_helper(context, betaEtaLongNormalform(context, term))
  }

  private class ContextImpl(val kind : ContextKind,
                            val depth : Integer,
                            val created : ContextKind.Created,
                            val parentContext : Option[ContextImpl],
                            val constants : Map[Name, Type]) extends Context 
  {
    
    def debugPrint(name : String) {
      var kinds : List[ContextKind] = List()
      var impl : ContextImpl = this
      while (impl != null) {
        kinds = impl.kind :: kinds
        impl.parentContext match {
          case None => impl = null
          case Some(c) => impl = c
        }
      }
      println("Context " + name+":")
      for (kind <- kinds) {
        println("  " + kind)
      }
    }

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

    def certify(term : Term) : CTerm = {
      typeOfTerm(term) match {
        case None => failwith("term is invalid in this context")
        case Some(ty) => mk_cterm(this, term, ty)
      }
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
       n == Kernel.exists.name)
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
          constants + (const_name -> ty))
    } 

    def assume(_assumption : CTerm) : Theorem = {
      if (isComplete) failwith("cannot extend completed context")
      val assumption = doautolift(_assumption)
      if (assumption.typeOf != Prop)
        failwith("assumption is not a valid proposition")
      val context = 
        new ContextImpl(
          ContextKind.Assume(assumption.term),
          depth + 1,
          created,
          Some(this),
          constants)
      mk_theorem(context, assumption.term)
    }

    def magic(term : Term) : Theorem = {
      if (typeOfTerm(term) != Some(Prop))
        failwith("term is not a valid proposition in this context")
      mk_theorem(this, term)      
    }

    def hasAssumptions : Boolean = {
      var context : Context = this
      do {
        context.kind match {
          case _ : ContextKind.Assume => return true
          case _ =>
        }
        context = context.parentContext match { case Some(c) => c case None => null }
      } while (context != null)
      false
    }

    def define(const_name : Name, tm_ : CTerm) : Theorem = {
      if (isComplete) failwith("cannot extend completed context")
      ensureContextScope(const_name)
      if (contains(const_name, constants) || isPolyConst(const_name))
        failwith("constant name "+const_name+" clashes with other constant in current scope")
      val tm = doautolift(tm_)
      val ty = tm.typeOf
      val eq = Comb(Comb(PolyConst(Kernel.equals, ty), Const(const_name)), tm.term)
      val context = 
        new ContextImpl(
          ContextKind.Define(const_name, ty, tm.term),
          depth + 1,
          created,
          Some(this),
          constants + (const_name -> ty))
      mk_theorem(context, eq)         
    }

    def choose(const_name : Name, thm : Theorem) : Theorem = {
      if (isComplete) failwith("cannot extend completed context")
      checkTheoremContext(thm)
      ensureContextScope(const_name)
      if (contains(const_name, constants) || isPolyConst(const_name))
        failwith("constant name "+const_name+" clashes with other constant in current scope")
      val (quantifiers, th) = strip_forall_unique(thm.proposition)
      val (x, ty, p) = 
        dest_exists(th) match {
          case None =>
            failwith("choose: theorem is not an (possibly universally quantified) existential")
          case Some(u) => u
        }
      var c : Term = Const(const_name)
      var cty : Type = ty
      for ((x, xty) <- quantifiers) {
        c = Comb(c, Var(x))
      }
      var prop = substVar(p, x, c)
      for ((x, xty) <- quantifiers.reverse) {
        cty = Fun(xty, cty)
        val all = PolyConst(Kernel.forall, xty)
        prop = Comb(all, Abs(x, xty, prop))
      }
      val context = 
        new ContextImpl(
              ContextKind.Choose(const_name, cty, prop),
              depth + 1,
              created,
              Some(this),
              constants + (const_name -> cty))
      mk_theorem(context, prop)             
    }
    
    def instantiate(thm : Theorem, cinsts : List[Option[CTerm]]) : Theorem = {
      checkTheoremContext(thm)
      def m(t : Option[CTerm]) : Option[Term] = {
        t match {
          case None => None
          case Some(t) => 
            Some(doautolift(t).term)
        }
      }
      val insts = cinsts.map(m _)
      mk_theorem(this, KernelUtils.instantiate(this, thm.proposition, insts))
    } 
            
    def checkTheoremContext(thm : Theorem) {
      if (KernelImpl.this != thm.context.kernel)   
        failwith("theorem belongs to a different kernel")
      if (thm.context != this)
        failwith("theorem belongs to a different context")      
    }

/*    def checkTermContext(term : CTerm) {
      if (KernelImpl.this != term.context.kernel)   
        failwith("cterm belongs to a different kernel")
      if (term.context != this)
        failwith("cterm belongs to a different context")      
    }*/

    def lift(thm : Theorem, preserve_structure : Boolean) : Theorem = {
      if (KernelImpl.this != thm.context.kernel)
        failwith("theorem belongs to a different kernel")
      val src_context = thm.context.asInstanceOf[ContextImpl]
      if (src_context == this) return thm
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

    def lift(term : CTerm, preserve_structure : Boolean) : CTerm = {
      if (KernelImpl.this != term.context.kernel)
        failwith("term belongs to a different kernel")
      val src_context = term.context.asInstanceOf[ContextImpl]
      if (src_context == this) return term
      val src_namespace = src_context.namespace
      if (namespace != src_namespace) {
        if (created.ancestorNamespaces.contains(src_namespace)) {
          val ct = completedContext(src_namespace).liftLocally(term, preserve_structure)
          if (!isQualifiedTerm(ct.term))
            failwith("cannot lift term containing unqualified constants between namespaces")
          mk_cterm(this, ct.term, ct.typeOf)
        } else {
          failwith("cannot lift term from namespace '" + src_context.namespace +"' to namespace '"+namespace+"'")
        }
      } else {
        liftLocally(term, preserve_structure)
      }
    }

    def autolift(term : CTerm) : Option[CTerm] = {
      val liftedTerm = lift(term, false)
      if (liftedTerm != term) None else Some(liftedTerm)
    }

    private def doautolift(term : CTerm) : CTerm = {
      val liftedTerm = lift(term, false)
      if (liftedTerm != term) failwith("cannot lift term unchanged int context") else liftedTerm
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
    
    // Same as lift, but assumes that the termcontext has the same namespace as this context.
    private def liftLocally(term : CTerm, preserve_structure : Boolean) : CTerm = {
      val src_context = term.context.asInstanceOf[ContextImpl]
      val common_ancestor = findCommonAncestorContext(this, src_context)
      val lifted_term = common_ancestor.liftLocallyUp(term, preserve_structure)
      if (common_ancestor.depth == depth)
        lifted_term
      else
        mk_cterm(this, lifted_term.term, lifted_term.typeOf)
    }

    private def liftLocallyUp(thm : Theorem, preserve_structure : Boolean) : Theorem = {
      import ContextKind._
      var context = thm.context.asInstanceOf[ContextImpl]
      if (context == this) return thm
      var prop = thm.proposition      
      if (preserve_structure) {
        while (context.depth > depth) {
          context.kind match {
            case Assume(hyp) => 
              prop = mk_implies(hyp, prop)
            case Introduce(c, ty) => 
              prop = mk_forall(c, ty, prop)
            case Define(c, ty, _) =>
              prop = mk_exists(c, ty, prop)
            case Choose(c, ty, _) =>
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
            case Assume(hyp) => 
              prop = mk_implies_prenex(hyp, prop)
              consts = collectConsts(hyp, consts)
            case Introduce(c, ty) => 
              if (consts.contains(c)) {
                prop = mk_forall(c, ty, prop)
                consts = consts - c
              }
            case Define(c, ty, _) =>
              if (consts.contains(c)) {
                prop = mk_exists(c, ty, prop)
                consts = consts - c
              }
            case Choose(c, ty, _) =>
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

    private def liftLocallyUp(cterm : CTerm, preserve_structure : Boolean) : CTerm = {
      import ContextKind._
      var context = cterm.context.asInstanceOf[ContextImpl]
      if (context == this) return cterm
      var term = cterm.term      
      var typeOf = cterm.typeOf
      if (preserve_structure) {
        while (context.depth > depth) {
          context.kind match {
            case Introduce(c, ty) => 
              term = mk_abs(c, ty, term)
            case Define(c, ty, _) =>
              term = mk_abs(c, ty, term)
            case Choose(c, ty, _) =>
              term = mk_abs(c, ty, term)
            case _ => 
              // nothing to do, the context does not introduce any constants
          }
          context = context.parentContext.get
        }
      } else {
        var consts : Set[Name] = collectConsts(term)
        while (context.depth > depth) {
          context.kind match {
            case Introduce(c, ty) => 
              if (consts.contains(c)) {
                term = mk_abs(c, ty, term)
                typeOf = Type.Fun(ty, typeOf)
                consts = consts - c
              }
            case Define(c, ty, _) =>
              if (consts.contains(c)) {
                term = mk_abs(c, ty, term)
                typeOf = Type.Fun(ty, typeOf)
                consts = consts - c
              }
            case Choose(c, ty, _) =>
              if (consts.contains(c)) {
                term = mk_abs(c, ty, term)
                typeOf = Type.Fun(ty, typeOf)
                consts = consts - c
              }
            case _ => 
              // nothing to do, the context does not introduce any constants
          }
          context = context.parentContext.get
        }        
      }
      mk_cterm(context, term, typeOf)
    }
    
    private def getTypeOfTerm(tm : Term) : Type = {
      typeOfTerm(tm) match {
        case None => failwith("term is not wellformed in this context")
        case Some(ty) => ty
      }
    }

    private def equivalent(u : Term, v : Term) : Boolean = {
      if ((u eq v) || u == v) return true
      val f = betaEtaNormalform(u)
      val g = betaEtaNormalform(v)
      alpha_equivalent(f, g)
    }

    private def equivalent(u : CTerm, v : CTerm) : Boolean = {
      u == v
    }
  
    def reflexive(tm_ : CTerm) : Theorem = {
      val tm = doautolift(tm_)
      val a = tm.term
      val ty = tm.typeOf
      mk_theorem(this, mk_equals(a, a, ty))
    }
    
    def normalize(tm_ : CTerm) : Theorem = {
      val tm = doautolift(tm_)
      val a = tm.term
      val ty = tm.typeOf
      val b = KernelUtils.betaEtaLongNormalform(this, a)
      mk_theorem(this, mk_equals(a, b, ty))      
    }

    def normalize(p : Theorem, q_ : CTerm) : Theorem = {
      checkTheoremContext(p)
      val q = doautolift(q_)
      if (equivalent(p.prop, q))
        mk_theorem(this, q.term)
      else 
        failwith("propositions are not alpha/beta/eta equivalent")
    }

    def mkFresh(name : IndexedName) : IndexedName = {
      def isFresh(name : Name) = 
        Kernel.isPolymorphicName(name) || typeOfConst(name).isEmpty
      var i : Utils.Integer = if (name.index.isDefined) name.index.get else 0
      do {
        val indexedName = IndexedName(name.name, if (i == 0) None else Some(i))
        if (isFresh(Name(None, indexedName)) && 
            isFresh(Name(Some(namespace), indexedName)))
          return indexedName
        i = i + 1
      } while (true)
      failwith("mkFresh: internal error")    
    }

    def destAbs(term_ : CTerm) : Option[(Context, CTerm, CTerm)] = {
      val term = doautolift(term_)
      term.term match {
        case Abs(name, ty, body) =>
          val x = Const(Name(Some(namespace), mkFresh(name)))
          val context = introduce(x.name, ty)
          val cx = mk_cterm(context, x, ty)
          val cbody = 
            term.typeOf match {
              case Fun(_, range) =>
                mk_cterm(context, KernelUtils.substVar(body, name, x), range)
              case _ => failwith("destAbs: internal error")
            }
          Some((context, cx, cbody))
        case _ => None
      }
    }

    // hugely inefficient operation, should not be necessary to recompute type each time
    def destComb(term : CTerm) : Option[(CTerm, CTerm)] = {
      doautolift(term).term match {
        case Comb(f, g) => Some(certify(f), certify(g))
        case _ => None
      }
    }

    def transitive(p : Theorem, q : Theorem) : Theorem = {
      checkTheoremContext(p)
      checkTheoremContext(q)
      val (a, b1, ty_a) = 
        dest_equals(p.proposition) match {
          case None => failwith("transitive: first theorem is not an equation")
          case Some(u) => u
        }
      val (b2, c, ty_c) = 
        dest_equals(q.proposition) match {
          case None => failwith("transitive: second theorem is not an equation")
          case Some(u) => u
        }
      if (ty_a == ty_c && equivalent(b1, b2))
        mk_theorem(this, mk_equals(a, c, ty_a))
      else
        failwith("transitive: middle propositions are not equivalent")
    }
    
    def comb(p : Theorem, q : Theorem) : Theorem = {
      checkTheoremContext(p)
      checkTheoremContext(q)
      val (f, g, fun_ty) = 
        dest_equals(p.proposition) match {
          case None => failwith("comb: first theorem is not an equation")
          case Some(u) => u
        }
      val (a, b, arg_ty) = 
        dest_equals(q.proposition) match {
          case None => failwith("comb: second theorem is not an equation")
          case Some(u) => u
        }
      fun_ty match {
        case Fun(domain, range) if domain == arg_ty =>
          mk_theorem(this, mk_equals(Comb(f, a), Comb(g, b), range))
        case _ =>
          failwith("comb: types do not match up")
      }
    }
    
    def modusponens(p : Theorem, q : Theorem) : Theorem = {
      checkTheoremContext(p)
      checkTheoremContext(q)
      def mk(antecedent : Term, conclusion : Term) : Theorem = {
        if (equivalent(p.proposition, antecedent))
          mk_theorem(this, conclusion)
        else
          failwith("modusponens: antecedents do not match")
      }
      dest_equals(q.proposition) match {
        case Some((a, b, _)) => mk(a, b)
        case None =>
          dest_implies(q.proposition) match {
            case Some((a, b)) => mk(a, b)
            case None => failwith("modusponens: equality or implication expected as second theorem")
          }
      }
    }
    
    def abs(p : Theorem) : Theorem = {
      checkTheoremContext(p)
      val (x, xty, body) = 
        dest_forall(p.proposition) match {
          case None => failwith("abs: theorem is not a universal quantification")
          case Some(u) => u
        }
      val (a, b, ty) = 
        dest_equals(body) match {
          case None => failwith("abs: theorem is not a universally quantified equality")
          case Some(u) => u
        }
      val left = Abs(x, xty, a)
      val right = Abs(x, xty, b)
      mk_theorem(this, mk_equals(left, right, Fun(xty, ty)))
    }
    
    def equiv(p : Theorem, q : Theorem) : Theorem = {
      checkTheoremContext(p)
      checkTheoremContext(q)
      (dest_implies(p.proposition), dest_implies(q.proposition)) match {
        case (Some((a,b)), Some((b_, a_))) =>
          if (equivalent(a, a_) && equivalent(b, b_)) 
            mk_theorem(this, mk_equals(a, b, Prop))
          else
            failwith("equiv: conclusion and hypothesis pairs do not match up")
        case _ => 
          failwith("equiv: two implications expected")
      }
    }

    def localConstants : Set[Name] = {
      var set : Set[Name] = Set()
      if (namespace == Kernel.root_namespace) {
        set = set + Kernel.forall + Kernel.equals + Kernel.exists
      }
      for ((name, _) <- constants) {
        if (!name.namespace.isDefined || name.namespace == Some(namespace)) {
          set = set + name
        }
      }
      set
    }

  }

  private case class NamespaceInfo(parents : Set[Namespace], aliases : Aliases)
  
  private var namespaces : Map[Namespace, Context] = Map()
  private var namespaceInfo : Map[Namespace, NamespaceInfo] = Map()
  
  def completedNamespaces = namespaces.keySet
  
  def contextOfNamespace(namespace : Namespace) : Option[Context] = namespaces.get(namespace)

  def parentsOfNamespace(namespace : Namespace) : Option[Set[Namespace]] = 
    namespaceInfo.get(namespace).map(_.parents)

  def aliasesOfNamespace(namespace : Namespace) : Option[Aliases] =
    namespaceInfo.get(namespace).map(_.aliases) 
  
  private def completedContext(namespace : Namespace) : ContextImpl = {
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
    val constants = ctx.constants.filterKeys(n => isQualifiedName(n))   
    val completedContext = 
      new ContextImpl(
          ContextKind.Complete,
          ctx.depth + 1,
          ctx.created,
          Some(ctx),
          constants)  
    namespaces += (namespace -> completedContext)
    completedContext
  }

  def restoreCompletedNamespace(parents : Set[Namespace], aliases : Aliases, context : Context) {
    if (!context.isInstanceOf[ContextImpl] || context.kernel != this) 
      failwith("context does not belong to this kernel")
    val namespace = context.namespace
    if (namespaces.contains(namespace)) 
      failwith("this namespace has already been completed: " + namespace)
    namespaces += (namespace -> context)
    namespaceInfo = namespaceInfo + (namespace -> new NamespaceInfo(parents, aliases))
  }
  
  def createNewNamespace(namespace : Namespace, parents : Set[Namespace], aliases : Aliases) : Context = {
    var ancestors : Set[Namespace] = Set()
    if (parentsOfNamespace(namespace).isDefined)
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
    val constants : Map[Name, Type] =
      if (namespace == Kernel.root_namespace) 
        Map(Kernel.implies -> Type.Fun(Type.Prop, Type.Fun(Type.Prop, Type.Prop)))
      else 
        Map()
    namespaceInfo = namespaceInfo + (namespace -> new NamespaceInfo(parents, aliases))
    new ContextImpl(
      created,
      0,
      created,
      None,
      constants)
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
    while (context1 != context2) {
      (context1.parentContext, context2.parentContext) match {
        case (Some(c1), Some(c2)) =>
          context1 = c1
          context2 = c2
        case _ =>
          failwith("no common ancestor context found")
      }
    }
    context1
  }

  import proofpeer.proofscript.serialization.UniquelyIdentifiableStore

  private class Serializers(store : UniquelyIdentifiableStore) extends KernelSerializers {
    import proofpeer.general._
    import proofpeer.proofscript.serialization._

    private val N = new NameSerializers(store)

    val IndexedNameSerializer : Serializer[IndexedName] = N.IndexedNameSerializer
    
    val NamespaceSerializer : Serializer[Namespace] = N.NamespaceSerializer
    
    val NameSerializer : Serializer[Name] = N.NameSerializer

    val AliasSerializer : Serializer[Alias] = N.AliasSerializer

    val AliasesSerializer : Serializer[Aliases] = N.AliasesSerializer

    private val T = new CustomizableTermSerializer(store, IndexedNameSerializer, NameSerializer)

    val TypeSerializer : Serializer[Type] = T.TypeSerializer

    val TermSerializer : Serializer[Term] = T

    val ContextKindSerializer = new CustomizableContextKindSerializer(store, TermSerializer, TypeSerializer, 
      NamespaceSerializer, NameSerializer)
 
    private class ContextImplSerializer extends Serializer[ContextImpl] {

      val cis = new UniquelyIdentifiableSerializer(store, this, UISTypeCodes.CONTEXT)

      val serializer = QuintupleSerializer(ContextKindSerializer, BigIntSerializer, 
        new TypecastSerializer[ContextKind.Created, ContextKind](ContextKindSerializer),
        OptionSerializer(cis), MapSerializer(NameSerializer, TypeSerializer))

      def serialize(c : ContextImpl) : Any = serializer.serialize((c.kind, c.depth, c.created, c.parentContext, c.constants))

      def deserialize(b : Any) : ContextImpl = {
        val t = serializer.deserialize(b)
        new ContextImpl(t._1, t._2, t._3, t._4, t._5)
      }

    }

    val ContextSerializer : Serializer[Context] = new TypecastSerializer[Context, ContextImpl](
      new UniquelyIdentifiableSerializer(store, new ContextImplSerializer, UISTypeCodes.CONTEXT))

    private object BasicCTermSerializer extends TransformSerializer[CTerm, (Context, Term, Type)](
      TripleSerializer(ContextSerializer, TermSerializer, TypeSerializer), (ct : CTerm) => (ct.context, ct.term, ct.typeOf), mk_cterm.tupled)

    object CTermSerializer extends UniquelyIdentifiableSerializer(store, BasicCTermSerializer, UISTypeCodes.CTERM)

    private object BasicTheoremSerializer extends TransformSerializer[Theorem, CTerm](
      CTermSerializer, (th : Theorem) => th.prop, (ct : CTerm) => mk_theorem(ct.context, ct.term))

    object TheoremSerializer extends UniquelyIdentifiableSerializer(store, BasicTheoremSerializer, UISTypeCodes.THEOREM)


  }

  def serializers(store : UniquelyIdentifiableStore) : KernelSerializers = {
    new Serializers(store)
  }

}


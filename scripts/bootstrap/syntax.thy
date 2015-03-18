theory Syntax
extends List

# Fail if nil
def assertNotNil x =
  if x == nil then assert false else x

# Fail if not a theorem. Return nil.
def
  assertThm (thm: Theorem) = nil
  assertThm _              = fail "Theorem required."

def
  assertTerm (term: Term) = nil
  assertTerm _            = fail "Term required."

# Basic term manipulation

def rator fx =
  match destcomb fx
    case [f,_] => f
    case _     => nil

def rand fx =
  match destcomb fx
    case [_,x] => x
    case _     => nil

def iscomb tm = destcomb tm <> nil
def isabs tm  = destabs tm <> nil

def
  desteq '‹_› = ‹_›' as tm = [rand (rator (tm:Term)), rand (tm:Term)]
  desteq tm                = assertTerm tm

def lhs tm =
  match desteq tm
    case [l,_] => l
    case _     => nil

def rhs tm =
  match desteq tm
    case [_,r] => r
    case _     => nil

# Very simple matching.
def matcher [tm,pattern,inst] =
  def insertNew [t,v,inst] =
    def
      insert []                        = "Constant"
      insert ([s,u] <+ inst) if u == v =
        if s == t then
          [s,u] <+ inst
        else
          nil
      insert (u <+ inst) if u == v =
        if t == u then
          inst
        else [t,u] <+ inst
      insert (u <+ inst) =
        match insert inst
          case nil        => nil
          case "Constant" => "Constant"
          case inst       => u <+ inst
    insert inst
  def
    matcher [tm,pattern,inst,env] =
      match destcomb pattern
        case [f,x] =>
          match destcomb tm
            case [g,y] =>
              match matcher (g,f,inst,env)
                case nil   => nil
                case finst => matcher (y,x,finst,env)
            case _ => nil
        case _ =>
          match destabs pattern
            case [patternCtx,x,patternBod] =>
              val newInst
              context <patternCtx>
                match destabs tm
                  case [ctx,y,bod] =>
                    context <ctx>
                      newInst = matcher (bod,patternBod,inst,[y,x] <+ env)
                  case _ => nil
              newInst
            case nil =>
              match assoc [tm,env]
                case nil =>
                  match insertNew (tm,pattern,inst)
                    case "Constant" =>
                      if tm == pattern then
                        inst
                      else nil
                    case nil  => nil
                    case inst => inst
                case [v] =>
                  if pattern == v then
                    inst
                  else nil
  matcher (tm,pattern,inst,[])

def matchAntThen [imp,ant,f] =
  def
    mp ['∀ x. ‹imp› x',vs] =
      val (ctx,x,imp) = destabs imp
      context <ctx>
        return mp (imp,vs +> x)
    mp ['‹p› → ‹q›',vs] =
      val bnds = matcher (ant: Term,p,vs)
      if bnds == nil then return nil
      val inst =
        for bnd in bnds do
          match bnd
            case [x,v] => x
            case v     => v
      f (instantiate (imp <+ inst))
    mp ['‹p› = ‹q›',vs] =
      val bnds = matcher (ant: Term,p,vs)
      if bnds == nil then return nil
      val inst =
        for bnd in bnds do
          match bnd
            case [x,v] => x
            case v     => v
      f (instantiate (imp <+ inst))
    mp _ = nil
  mp (imp,[])

def matchmp (imp <+ ants) =
  for ant in ants do
    imp =
      matchAntThen (imp,rhs (normalize (ant: Term)),thm => modusponens (ant,thm))
    if imp == nil then
      return nil
  imp

context
  assume imp:'∀x z w. x → w ∧ w → x ∧ z ∧ w'
  let 'y:ℙ'
  let 'z:ℙ'
  let 'P:ℙ → ℙ'
  assume ant1:'y:ℙ'
  assume ant2:'P z ∧ P z'
  assert (matchmp [imp,ant1,ant2]: Term) == '∀ x : ℙ. (y ∧ x) ∧ (P z)'

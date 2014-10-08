theory Match
extends List root

def matcher [tm,target,inst] =
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
    matcher [tm,target,inst,env] =
      match target
        case '∀ x. ‹p› x' =>
          match tm
            case '∀ x. ‹q› x' => matcher (q,p,inst,env)
            case _            => nil
        case '∃ x. ‹p› x' =>
          match tm
            case '∀ x. ‹q› x' => matcher (q,p,inst,env)
            case _            => nil
        case _ =>
          match destcomb target
            case [f,x] =>
              match destcomb tm
                case [g,y] =>
                  match matcher (g,f,inst,env)
                    case nil   => nil
                    case finst => matcher (y,x,finst,env)
                case _ => nil
            case _ =>
              match destabs target
                case [targetCtx,x,targetBod] =>
                  val newInst
                  context <targetCtx>
                    match destabs tm
                      case [ctx,y,bod] =>
                        context <ctx>
                          newInst = matcher (bod,targetBod,inst,[y,x] <+ env)
                      case _ => nil
                  newInst
                case nil =>
                  match assoc [tm,env]
                    case nil =>
                      match insertNew (tm,target,inst)
                        case "Constant" =>
                          if tm == target then
                            inst
                          else nil
                        case nil  => nil
                        case inst => inst
                    case [v] =>
                      if target == v then
                        inst
                      else nil
  matcher (tm,target,inst,[])

def matchAntThen [imp,ant,f] =
  def
    mp ['∀ x. ‹imp› x',vs] =
      val (ctx,x,imp) = destabs imp
      context <ctx>
        return mp (imp,vs +> x)
    mp ['‹p› → ‹q›',vs] =
      val bnds = matcher (term ant,p,vs)
      if bnds == nil then return nil
      val inst =
        for bnd in matcher (term ant,p,vs) do
          match bnd
            case [x,v] => x
            case v     => v
      f (instantiate (imp <+ inst))
    mp ['‹p› = ‹q›',vs] =
      val bnds = matcher (term ant,p,vs)
      if bnds == nil then return nil
      val inst =
        for bnd in matcher (term ant,p,vs) do
          match bnd
            case [x,v] => x
            case v     => v
      f (instantiate (imp <+ inst))
    mp _ = nil
  mp (imp,[])

def matchmp (imp <+ ants) =
  for ant in ants do
    imp = matchAntThen (imp,ant,thm => modusponens (ant,thm))
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
  show term(matchmp(imp,ant1,ant2))

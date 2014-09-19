theory \issue35 extends \root

def
  assoc [_,[]] = nil
  assoc [k,(theKey,v) <+ kvs] =
    if k == theKey then
      [v]
    else
      assoc [k,kvs]

val matcher = [tm,target,vars] =>
  val insertNew = [t,v,inst] =>
    def
      insert []                        = "Constant/Bound"
      insert ([s,u] <+ inst) if u == v =
        if s == t then
          [s,u] <+ inst
        else
          nil
      insert (u <+ inst)     if u == v = [t,u] <+ inst
      insert (u <+ inst) =
        match insert inst
          case nil              => nil
          case "Constant/Bound" => "Constant/Bound"
          case inst             => u <+ inst
    insert inst
  def
    matcher [tm,target,inst,env] =
      show tm
      show target
      show env
      match target
        case '∀ x. ‹p› x' =>
          match tm
            case '∀ x. ‹q› x' => matcher [p,q,inst,env]
            case _            => nil
        case '∃ x. ‹p› x' =>
          match tm
            case '∀ x. ‹q› x' => matcher [p,q,inst,env]
            case _            => nil
        case _ =>
          match destabs target
            case [targetCtx,x,targetBod] =>
              match destabs tm
                case [ctx,y,bod] =>
                  val newInst
                  context <targetCtx>
                    context <ctx>
                      newInst = matcher [bod,targetBod,inst,[x,y] <+ env]
                  newInst
                case _ => nil
            case nil =>
              match insertNew [tm,target,inst]
                case "Constant/Bound" =>
                  match assoc [tm,env]
                    case nil =>
                      if tm == target then
                        inst
                      else
                        nil
                    case [targetV] =>
                      if targetV == target then
                        inst
                      else nil
                case nil  => nil
                case inst => inst
  matcher [tm,target,vars,[]]

failure show matcher ['∀ x. x ∧ x', '∀ y. y ∧ y', []]
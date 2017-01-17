theory HOLEmbedding
extends \bootstrap\Classical

def onNonNil [f,x] =
  if x == nil then nil else f x

def onNonNil2 [f,x,y] =
  if x == nil or y == nil then nil else f [x,y]

# vap_codom
# vfun_type
# vfun_space_inhabited
# bool_inhabited
# unveq
# beta_thm
# abs_thm
# mangle_type
# veq_const
# veq
# vfun_type
# two_elements
# ty_string
# embed_ty_ctx
# mangle_cost
# mk_vap
# mk_vfun
# exists_triv

context

  # A HOL type is one of:
    - a HOL type variable, represented by its name as a string. These appear in code
      with identifiers like "tyvar";
    - a type application, represented by a vector of the form cons <+ tys where cons
      is the name of the constructor as a string, and where tys are a vector of type
      arguments.

  # An HOL term is one of:
    - a HOL variable, represented by a triple whose first component is "V", whose
      second component is the variable name as a string, and whose third component is
      the variable type. The variable name appears in code with identifiers like
      "?name"
    - a HOL constant is represented by ["C", name, ty] where name and ty are the
      name and type of the constant.
    - a combination, represented by a pair whose first component is the rator and
      whose second component is the rand.
    - an abstraction, represented by ["λ", xname, ty, bod] where xname is the name of
      the bound variable as a string, xty is its type, and bod is the body.

  # HOL theorems are embedded as a triple. The components are:
    1. an "embedding context", being a dictionary with fields:
       - "context": the context in which embedded type variables and free variables
         with their constraints have been introduced.
       - "tyvars": the list of type variables in the order that they have been
         introduced.
       - "vars": variable/type pairs in the order that they have been introduced.
       - "tyctx": see documentation for embed_ty_ctx below
       - "vctx": a map from variable/type pairs to the embedded typing theorems
    2. a ProofScript theorem as described in HOLEmbedding.org;
    3. a typing tree, mirroring the term tree, and giving embedded typing judgements
    for each subterm.

  # Throughout code, "e" prefixes variables which refer to embedded proofscript terms
    and theorems.

  let 'eq : 𝒰 → 𝒰'
  let 'fnspace : 𝒰 → 𝒰 → 𝒰'
  let 'zero = ∅'
  let 'one = {∅}'
  let bool_tm:'bool = {zero,one}'
  let 'is_true = (p ↦ (p = one))'
  assume fun_spec  : '∀A f p. p ∈ fun A f = (∃x. x ∈ A ∧ p = (x, f x))'
  assume eq_def  : '∀A. eq A = fun A (x ↦ fun A (y ↦ ifThenElse (x=y) {∅} ∅))'
  assume eq_type : '∀A. eq A ∈ fnspace A (fnspace A bool)'
  assume apply_codom : '∀A B f x. f ∈ fnspace A B ∧ x ∈ A → f x ∈ B'
  assume fnspace_inh : '∀A B. (∃x. x ∈ B) → (∃f. f ∈ fnspace A B)'
  assume fun_inh : '∀A B f. (fun A f ∈ fnspace A B) = (∀x. x ∈ A → f x ∈ B)'
  assume eq_spec : '∀A x y. x ∈ A ∧ y ∈ A → (x = y) = (is_true (eq A x y))'
  val eq_spec_sym = gsym eq_spec
  assume eq_ty : '∀A. eq A ∈ fnspace A (fnspace A bool)'
  assume eq_applied_ty : '∀A x y. x ∈ A ∧ y ∈ A → eq A x y ∈ bool'
  assume eq_applied_partial_ty : '∀A x. x ∈ A → eq A x ∈ fnspace A bool'
  val fun_inh_sym = gsym fun_inh

  def ty_match [ty1,ty2] =
    def tys_match [tys1,tys2] =
      match [tys1,tys2]
        case [[],[]] => {→}
        case [ty1 <+ tys1, ty2 <+ tys2] =>
          val inst  = ty_match [ty1,ty2]
          val insts = tys_match [tys1,tys2]
          onNonNil2 [[xs,ys] => xs ++ ys, inst, insts]
    match [ty1,ty2]
      case [tyvar:String, ty] => { tyvar → ty }
      case [cons1 <+ args1,cons2 <+ args2] if cons1 == cons2 =>
        tys_match [args1,args2]
      case _ => nil

  # embed_ty_ctx

     Convert a HOL type to an embedded type
       tyctx: a dictionary sending:
       - type variable names to embedded inhabitation theorems
       - type constructor names wrapped in singleton lists to a pair [ety,ty_inh]
         where ety is the embedded type constructor and ty_inh its inhabitation
         theorem.

  def
    embed_ty_ctx [tyctx,["fun",domty,codomty]] =
      val edomty = embed_ty_ctx [tyctx,domty]
      val ecodomty = embed_ty_ctx [tyctx,codomty]
      'fnspace ‹edomty› ‹ecodomty›'
    embed_ty_ctx [tyctx,cons <+ tyargs] =
      val [econs,_] = tyctx [cons]
      val eargtys = map [(arg => embed_ty_ctx [tyctx,arg]), tyargs]
      foldl [([ety,eargty] => '‹ety› ‹eargty›'),eargtys,econs]
    embed_ty_ctx [tyctx,tyvar] =
      val '∃x. x ∈ ‹ety›' = tyctx tyvar
      ety

  # embed_tm_ctx

     Convert a HOL term to an embedded term
       tyctx: as for embed_ty_ctx
       vctx: a dictionary sending variable name/type pairs (HOL supports overloading)
         to a list of theorems asserting that the embedded term belongs to the
         embedded type

       constants: a dictionary sending a constant name to a tuple
       [registered_ty,tyvars,c_is_ty]

       - registered_ty: the HOL type used in new_constant

       - tyvars: a list [tyvar1,tyvar2,…,tyvarn] such that, after matching the
         requested type with the registered type to give the substitution
            tyvar1 -> ety1
            tyvar2 -> ety2
            ...
            tyvarn -> etyn
          we have that the embedded constant is
           '‹c› <ety1› <ety2› … <etyn›'

       - c_is_ty: a theorem asserting that the embeded constant belongs to its
         embedded type on condition of its embedded type arguments being inhabited.

  def
    embed_tm_ctx [tyctx,vctx,constants,["V",name,ty]] =
      val ev <+ _ = vctx [name,ty]
      [ev]
    embed_tm_ctx [tyctx,vctx,constants,["C",name,ty]] =
      val [registered_ty,tyvars,c_is_ty] = constants name

      # TODO: Can we get match failures here?
      val inst = ty_match [registered_ty,ty]

      def
        prove_ty_inh ["fun",domty,codomty] =
          val codom_inh = prove_ty_inh codomty
          modusponens [codom_inh,
                       instantiate [fnspace_inh,
                                    embed_ty_ctx [tyctx,domty],
                                    embed_ty_ctx [tyctx,codomty]]]
        prove_ty_inh (cons <+ tyargs) =
          def f [thm,ty] =
            modusponens [prove_ty_inh ty,
                         instantiate [thm,embed_ty_ctx [tyctx,ty]]]
          val [_,ty_inh] = tyctx [cons]
          foldl [f,tyargs,ty_inh]
        prove_ty_inh tyvar = tyctx tyvar

      def f [ty,thm] =
        val ty2 = inst ty
        val thm = instantiate [thm,embed_ty_ctx [tyctx,ty2]]
        match thm
          case '∃x. x ∈ ‹ty3› → ‹_›' if ty2 == ty3 =>
            modusponens [prove_ty_inh ty2,thm]
          case _ => thm
      [foldr [f,tyvars,c_is_ty]]

    embed_tm_ctx [tyctx, vctx, constants, [f,x]] =
      val (('‹ef› ∈ fnspace ‹_› ‹eyty›' as fthm) <+ _) as ftree =
        embed_tm_ctx [tyctx,vctx,constants,f]
      val (('‹ex› ∈ ‹exty›' as xthm) <+ _) as xtree =
        embed_tm_ctx [tyctx,vctx,constants,x]
      val fxthm = modusponens [andIntro [fthm,xthm],
                               instantiate [apply_codom,exty,eyty,ef,ex]]
      [fxthm,ftree,xtree]

    embed_tm_ctx [tyctx, vctx, constants, ["λ",xname,xty,bod]] =
      val bod_thm
      val bodtree
      context
        let ex:'‹fresh xname›'
        assume x_is_ty:'‹ex› ∈ ‹embed_ty_ctx [tyctx,xty]›'
        val is_xty_stack = vctx [xname,xty]
        val vctx = vctx ++ { [xname,xty] → if is_xty_stack == nil then [x_is_ty]
                                           else x_is_ty <+ is_xty_stack }
        (bod_thm <+ _) as bodtree = embed_tm_ctx [tyctx, vctx, constants, bod]
        bod_thm = lift! bod_thm
      val '∀x. x ∈ ‹exty› → ‹ef› x ∈ ‹ebodty›' = bod_thm
      [modusponens [bod_thm, instantiate [fun_inh_sym, exty, ebodty, ef]], bodtree]

    mk_tyctx [acc,[],[]] =
      acc ++ { "context" → context }
    mk_tyctx [acc,["fun",domty,codomty] <+ tys,tms] =
      mk_tyctx [acc,domty <+ codomty <+ tys,tms]
    mk_tyctx [acc,(cons <+ tyargs) <+ tys,tms] =
      mk_tyctx [acc,tyargs ++ tys,tms]
    mk_tyctx [acc,tyvar <+ tys,tms] =
      val tyctx = acc "tyctx"
      if tyctx tyvar == nil then
        let ety:'‹fresh tyvar›'
        assume ty_inh:'∃x. x ∈ ‹ety›'
        val tyctx = tyctx ++ { tyvar → ty_inh }
        val tyvars = acc "tyvars" +> tyvar
        mk_tyctx [acc ++ { "tyctx" → tyctx, "tyvars" → tyvars },tys,tms]
      else mk_tyctx [acc,tys,tms]
    mk_tyctx [acc,[],["V",xname,ty] <+ tms] =
      val vctx = acc "vctx"
      if not (acc "bounds" [xname,ty]) and vctx [xname,ty] == nil then
        val acc = mk_tyctx [acc,[ty],[]]
        context <acc "context">
          let ex:'‹fresh xname›'
          val ety = embed_ty_ctx [acc "tyctx",ty]
          assume x_is_ty:'‹ex› ∈ ‹ety›'
          val vctx = vctx ++ { [xname,ty] → [x_is_ty] }
          val vars = acc "vars" +> [xname,ty]
          return mk_tyctx [acc ++ { "vctx" → vctx, "vars" → vars },[],tms]
       else mk_tyctx [acc,[],tms]
    mk_tyctx [acc,[],["C",_,ty] <+ tms] =
      mk_tyctx [acc,[ty],tms]
    mk_tyctx [acc,[],[f,x] <+ tms] =
      mk_tyctx [acc,[],f <+ x <+ tms]
    mk_tyctx [acc,[],["λ",xname,ty,bod] <+ tms] =
      val bounds = acc "bounds"
      val acc =
        mk_tyctx [acc ++ { "bounds" → bounds ++ {[xname,ty]} },[ty],[bod]]
      context <acc "context">
        return mk_tyctx [acc ++ { "bounds" → bounds },[],tms]

  # Embed types and terms, additionally returning a typing tree for embed_tm.  We
    also return an embedding context.

  def initAcc tyctx =
    {
      "tyctx"  → tyctx,
      "vctx"   → {→},
      "bounds" → {},
      "tyvars" → [],
      "vars"   → []     }

  val [embed_ty,embed_tm] =
    def
      embed_ty [tyctx,ty] =
        val acc = mk_tyctx [initAcc tyctx,[ty],[]]
        val ctx = acc "context"
        val ety
        context <acc "context">
          ety = embed_ty_ctx [acc "tyctx", ty]
        [acc -- {"bounds"},ety]
      embed_tm [tyctx,constants,tm] =
        val acc = mk_tyctx [initAcc tyctx,[],[tm]]
        val etm
        context <acc "context">
          etm = embed_tm_ctx [acc "tyctx", acc "vctx", constants, tm]
        [acc -- {"bounds"},etm]

    [embed_ty,embed_tm]

  theorem eq_refl: '∀A x. x ∈ A → (is_true (eq A x x))'
    let 'A'
    let 'x'
    let 'y'
    assume asm:'x ∈ A'
    modusponens [reflexive 'x',
                 modusponens [andIntro [asm,asm],
                              instantiate [eq_spec,'A','x','x']]]

  def
    assume_ty_conds '∀x. ‹p› x → ‹q› x' as thm =
      let x:'‹fresh "x"›'
      assume asm:'‹p› ‹x›'
      assume_ty_conds (modusponens [asm,instantiate [thm,x]])
    assume_ty_conds thm = [context,thm]

  # Given typing trees for terms x and y, produce the typing tree for x = y.
  def
    mk_eq_tree [(xty_thm <+ _) as xtree, (yty_thm <+ _) as ytree] =
      val [ctx,xty_thm] = assume_ty_conds xty_thm
      context <ctx>
        val [ctx,yty_thm] = assume_ty_conds yty_thm
        context <ctx>
          val '‹ex› ∈ ‹exty›' = xty_thm
          val '‹ey› ∈ ‹_›'    = yty_thm
          val ty_thm = modusponens [andIntro [xty_thm,yty_thm],
                                    instantiate [eq_applied_ty,exty,ex,ey]]
          val ty_thm2 =
            modusponens [xty_thm, instantiate [eq_applied_partial_ty, exty, ex]]
          return [ty_thm, [ty_thm2, [instantiate [eq_ty, exty]],
                                     xtree],
                           ytree]

  def
    refl [tyctx, constants, x] =
      val [ctx,xtree] = embed_tm [tyctx, constants, x]
      val thm
      val tree
      context <ctx "context">
        val (('‹ex› ∈ ‹exty›' as x_is_ty) <+ _) = xtree
        thm = modusponens [x_is_ty,instantiate [eq_refl, exty, ex]]
        tree = mk_eq_tree [xtree,xtree]
      [ctx,thm,tree]

  def
    assum [tyctx, constants, prop] =
      val [ctx,proptree] = embed_tm [tyctx, constants, prop]
      val thm
      context <ctx "context">
        match proptree
          case ('‹eprop› ∈ bool' <+ _) =>
            assume asm:'is_true ‹eprop›'
            thm = asm
          case _ =>
            return "Failure ASSUME: not a proposition"
      [ctx, thm, proptree]

  def
    assume_all [asms,'‹p› → ‹q›' as thm] =
      match asms p
        case nil =>
          assume asm:p
          assume_all [asms ++ {p → asm},modusponens [asm,thm]]
        case p => assume_all [asms,modusponens [p,thm]]
    assume_all [asms,thm] = [context,asms,thm]

  assume setcomb: '∀f g x y. f = g ∧ x = y → f x = g y'
  assume abs_thm: '∀A f g. (∀x. x ∈ A → f x = g x) → fun A f = fun A g'

  def
    map_tree_thms [f,[thm]] =
      [f thm]
    map_tree_thms [f,[fxthm,ftree,xtree]] =
      [f fxthm, map_tree_thms [f,ftree], map_tree_thms [f,xtree]]
    map_tree_thms [f,[absthm,bodtree]] =
      [f absthm, map_tree_thms [f,bodtree]]
    inst [v,ant,thm] =
      modusponens [ant,instantiate [thm,v]]

  def
    merge_ctxs [[xctx, xthm, xtree], [yctx, ythm, ytree]] =
      context <xctx "context">
        val tyctx = xctx "tyctx"
        val vctx  = xctx "vctx"
        val tys   = xctx "tyvars"
        val vs    = xctx "vars"
        val ythm = lift! ythm
        for ytyname in yctx "tyvars" do
          match tyctx ytyname
            case nil =>
              let ty:'‹fresh ytyname›'
              assume inh:'∃x. x ∈ ‹ty›'
              tys = tys +> [ty]
              tyctx = tyctx ++ { ytyname → inh}
              ythm = inst [ty,inh,ythm]
              ytree = map_tree_thms [thm => inst [ty,inh,lift! thm], ytree]
            case inh =>
              val '∃x. x ∈ ‹xty›' = inh
              ythm = inst [xty,inh,ythm]
              ytree = map_tree_thms [thm => inst [xty,inh,lift! thm], ytree]
        for [yvar,yty] in yctx "vars" do
          match vctx yvar
            case nil =>
              let x:'‹fresh yvar›'
              val ety = embed_ty_ctx [tyctx,yty]
              assume ty_inh:'‹x› ∈ ‹ety›'
              vs = vs +> [yvar,yty]
              vctx = vctx ++ { [yvar,yty] → ty_inh }
              ythm = inst [x,ty_inh,ythm]
              ytree = map_tree_thms [thm => inst [x,ty_inh,lift! thm], ytree]
            case ty_inh =>
              val '‹x› ∈ ‹_›' = ty_inh
              ythm = inst [x,ty_inh,ythm]
              ytree = map_tree_thms [thm => inst [x,ty_inh,lift! thm], ytree]
        val ectx = xctx ++ { "context" → context,
                             "tyctx" → tyctx,
                             "vctx" → vctx,
                             "tyvars" → tys,
                             "vars" → vs }
        val [ctx,asms,xthm] = assume_all [{→},xthm]
        context <ctx>
          val [ctx,asms,ythm] = assume_all [asms,ythm]
          return [ectx,xthm,xtree,ythm,ytree]

    mk_comb [fg,xy] =
      val [ctx,fgthm,fgtree,xythm,xytree] =
        merge_ctxs [fg,xy]
      context <ctx "context">
        val [_,
               [_, _, ('‹ef› ∈ ‹efty›' as f_is_ty) <+ _ as ftree],
               ('‹eg› ∈ ‹_›' as g_is_ty) <+ _ as gtree] = fgtree
        val [_,
               [_, _, ('‹ex› ∈ ‹exty›' as x_is_ty) <+ _ as xtree],
               ('‹ey› ∈ ‹_›' as y_is_ty) <+ _ as ytree] = xytree
        val fgthm =
          modusponens [fgthm,
                       modusponens [andIntro [f_is_ty,g_is_ty],
                                    instantiate [eq_spec_sym,efty,ef,eg]]]
        val xythm =
          modusponens [xythm,
                       modusponens [andIntro [x_is_ty,y_is_ty],
                                    instantiate [eq_spec_sym,exty,ex,ey]]]
        val 'fnspace ‹_› ‹erty›' = efty
        val fx_is_ty = modusponens [andIntro [f_is_ty,x_is_ty],
                                   instantiate [apply_codom, exty, erty, ef, ex]]
        val gy_is_ty = modusponens [andIntro [g_is_ty,y_is_ty],
                                   instantiate [apply_codom, exty, erty, eg, ey]]
        val '‹efx› = ‹egy›' as fgxy =
          modusponens [andIntro [fgthm,xythm],instantiate [setcomb,ef,eg,ex,ey]]
        val fgthm = modusponens [fgxy,
                                 modusponens [andIntro [fx_is_ty,gy_is_ty],
                                              instantiate [eq_spec,erty,efx,egy]]]
        return
          [ctx,
           fgthm,
           mk_eq_tree [[fx_is_ty,ftree,xtree], [gy_is_ty,gtree,ytree]]]

  theorem apply2: '∀X f x. x ∈ X → fun X f x = f x'
    let 'X'
    let 'f:𝒰 → 𝒰'
    let x:'x'
    assume asm:'x ∈ X'
    val thm = modusponens [instantiate [apply,'X','f'],
                           instantiate [forallin, 'X', 'x ↦ fun X f x = f x']]
    modusponens [asm, instantiate [thm,'x']]

  def
    beta [tyctx, constants, redex] =
      val [ctx,[redex_is_ty,
                 [abs_is_ty,(bod_is_ty <+ _) as bodtree],
                 (x_is_ty <+ _) as xtree] as tree] =
        embed_tm [tyctx, constants, redex]
      context <ctx "context">
        val '‹eredex› ∈ ‹_›' = redex_is_ty
        val '‹ex› ∈ ‹exty›' = x_is_ty
        val 'fun ‹_› ‹eabs› ∈ ‹_›' = abs_is_ty
        val '∀y. y ∈ ‹_› → ‹_› y ∈ ‹ebodty›' = bod_is_ty
        val betaeq = modusponens [x_is_ty,instantiate [apply2,exty,eabs,ex]]
        val betaeq =
          modusponens [betaeq,modusponens [andIntro [redex_is_ty,x_is_ty],
                                           instantiate [eq_spec,ebodty,eredex,ex]]]
        return [ctx,betaeq,mk_eq_tree [tree,bodtree]]

  def
    abs [constants, [xname,xty] as xvar, [ctx, eq_thm, eq_tree]] =
      val tyctx = ctx "tyctx"
      val eq_thm = lift! eq_thm
      val ty_inhs =
        for tyvar in ctx "tyvars" do
          let ety:'‹fresh tyvar›'
          assume ty_inh:'∃x. x ∈ ‹ety›'
          tyctx = tyctx ++ { tyvar → ty_inh }
          [tyvar,ty_inh]
      val acc = mk_tyctx [initAcc tyctx,[xty],[]]
      context <acc "context">
        val exty = embed_ty_ctx [acc "tyctx",xty]
        val left_is_tys = []
        val right_is_tys = []
        val v_ty_inhs =
          for [vname,vty] in ctx "vars" do
            if [vname,vty] == xvar then
              left_is_tys = right_is_tys
            else
              let ev:'‹fresh vname›'
              val evty = embed_ty_ctx [tyctx,vty]
              assume v_is_ty:'‹ev› ∈ ‹evty›'
              right_is_tys = right_is_tys +> v_is_ty
        def prove_conds ['‹ex› ∈ ‹_›' as x_is_ty,thm] =
          for [_,'∃x. x ∈ ‹ety›' as ty_inh] in ty_inhs do
            thm = modusponens [ty_inh, instantiate [thm, ety]]
          for '‹ev› ∈ ‹_›' as v_is_ty in left_is_tys do
            thm = modusponens [v_is_ty, instantiate [thm, ev]]
          match thm
            case '∀x. x ∈ «exty» → ‹_› x' =>
              thm = modusponens [x_is_ty, instantiate [thm, ex]]
            case _ =>
          for '‹ev› ∈ ‹_›' as v_is_ty in right_is_tys do
            thm = modusponens [v_is_ty, instantiate [thm, ev]]
          thm
        def
          prove_hyps ('∀x. x ∈ ‹_› → ‹p› → ‹q› x' as thm) =
            assume p
            theorem q:
              let ex:'‹fresh xname›'
              assume asm:'‹ex› ∈ ‹exty›'
              modusponens [asm, instantiate [thm,ex]]
            prove_hyps q
          prove_hyps ('∀x. x ∈ ‹_› → ‹p› x → ‹q› x' as thm) =
            return "Failure ABS"
          prove_hyps ('∀x. x ∈ ‹_› → is_true (eq ‹_› (‹px› x) (‹qx› x))' as thm) =
            theorem cond_eq_thm:
              let ex:'‹fresh xname›'
              assume asm:'‹ex› ∈ ‹exty›'
              val thm = modusponens [asm, instantiate [thm,ex]]
              val [_,[_,_,px_is_ty <+ _],qx_is_ty <+ _] = eq_tree
              val '‹_› ∈ ‹pxty›' as px_is_ty = prove_conds [asm,lift! px_is_ty]
              val qx_is_ty = prove_conds [asm,lift! qx_is_ty]
              modusponens
                [thm,
                 modusponens
                   [andIntro [px_is_ty,qx_is_ty],
                    instantiate [eq_spec_sym,pxty,'‹px› ‹ex›','‹qx› ‹ex›']]]
            cond_eq_thm
          prove_hyps thm = thm
        val x_is_ty
        context
          let x:'‹fresh xname›'
          assume x_is_ty_asm:'‹x› ∈ ‹exty›'
          x_is_ty = x_is_ty_asm
          eq_thm = prove_conds [x_is_ty,eq_thm]
        # TODO Add trees
        eq_thm = prove_hyps (lift! eq_thm)
        match eq_thm
          case _:Theorem =>
            val [ctx,_,eq_thm] = assume_all [{->},lift! eq_thm]
            context <ctx>
              match eq_thm
                case '∀x. x ∈ ‹_› → ‹f› x = ‹g› x' as thm =>
                  return modusponens [eq_thm,instantiate [abs_thm,exty,f,g]]
                case '‹fx› = ‹gx›' as thm =>
                  show fx
                  show gx
                  # modusponens [andIntro instantiate [eqspec,exty,'‹f› x','‹g› x']
          case failMsg => return failMsg

  let 'list:𝒰 → 𝒰'
  let 'append:𝒰 → 𝒰'
  let 'nil:𝒰 → 𝒰'
  let 'is_empty:𝒰 → 𝒰'

  assume list_inh:'∀a. (∃x. x ∈ a) → (∃x. x ∈ list a)'
  assume append_ty:'∀a. (∃x. x ∈ a) →
                      append a ∈ fnspace (list a) (fnspace (list a) (list a))'
  assume nil_ty:'∀a. (∃x. x ∈ a) → nil a ∈ list a'
  assume is_empty_ty:'∀a. (∃x. x ∈ a) → is_empty a ∈ fnspace (list a) bool'

  val constants =
    { "=" → [["fun","a","a"],
             ["a"],
             eq_type],
      "++" → [["fun",["list","a"],["fun",["list","a"],["list","a"]]],
              ["a"],
              append_ty],
      "nil" → [["list","c"],["c"],nil_ty],
      "is_empty" → [["fun",["list","d"],"bool"],["d"],is_empty_ty] }

  assume bool_inh: '∃x. x ∈ bool'

  val tyctx =
    { ["bool"] → ['bool',bool_inh],
      ["list"] → ['list',list_inh] }

  val tm = [[ ["C","++",["fun",["list","b"],["fun",["list","b"],["list","b"]]]],
              ["V","x",["list","b"]]],
             ["V","foo",["list","b"]]]

  val thm1 = refl [tyctx,constants,["V","f",["fun","a","a"]]]
  val thm2 = refl [tyctx,constants,["V","x","a"]]
  val thm3 =
    assum [tyctx,constants,
           [[["C","=",["fun","a","a"]],["V","x","a"]],["V","x","a"]]]
  val thm4 = refl [tyctx,constants,["V","x",["fun","a","b"]]]
  show mk_comb [thm1,thm2]
  show beta [tyctx,constants,[["λ","x","a",["V","x","a"]],["V","x","a"]]]
  show abs [constants,["x","a"],thm3]
  show abs [constants,["x",["fun","a","b"]],thm4]
  show abs [constants,["x",["fun","c","d"]],thm4]
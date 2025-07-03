import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm
import Hs.SynthInstance

set_option profiler true

@[simp]
def compile_ctor2variant : HsCtor2Variant -> Ctor2Variant
| .arrowk => .arrowk
| .appk => .appk
| .appt => .appt
| .app => .app

@[simp]
def compile_bind2variant : HsBind2Variant -> Bind2Variant
| .all => .all
| .arrow => .arrow
| .farrow => .arrow
| .lam => .lam
| .lamt => .lamt

-- TODO: move bind2_frame and hs_bind2_frame in a common place
@[simp]
def hs_bind2_frame : Term -> HsBind2Variant -> Frame Term
| t, .all => .kind t
| t, .lam => .type t
| t, .lamt => .kind t
| _ , _ =>  .empty


@[simp]
def compile_spine_variant : HsSpineVariant -> SpineVariant
| .term => .term
| .type => .type
| .kind => .kind

-- surface: datatype Bool (tt, ff); #0 = ff, #1 = tt, #2 = Bool <-- defined by hs_nth
abbrev DsM a := Except Std.Format a

namespace DsM

def ok : a -> DsM a := λ x => Except.ok x
def error : Std.Format -> DsM a := λ x => Except.error x
def bind : DsM a -> (a -> DsM b) -> DsM b := Except.bind

def toDsM (pfix : Std.Format) : Option a -> DsM a
| .some a => ok a
| .none => error (pfix ++ Std.Format.line)

def toDsMq : Option a -> DsM a := toDsM ""

def run [Repr a] : DsM a -> Std.Format
| .error e => "Error:" ++ Std.Format.line ++ e
| .ok t => repr t

end DsM

instance beq_DsMa [BEq a] : BEq (DsM a) where
     beq x y :=
       match (x, y) with
       | (.ok x, .ok y) => x == y
       | _ => False


@[simp]
def fresh_vars_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => fresh_vars_aux n (#n :: acc)

@[simp]
def fresh_vars : Nat -> List Term := λ n => fresh_vars_aux n []
@[simp]
def re_index_base := fresh_vars

#eval fresh_vars 3

-- theorem fresh_vars_aux_lemm : (fresh_vars_aux n l).length = l.length + n := by
-- sorry
-- theorem fresh_vars_lemma : (fresh_vars n).length == n := by
-- sorry

-- Get all the open methods for a given term
/- Caution: The ids themselves are meaningless (sort of),
  just depend on the size of the list. thats the width of the class-/
@[simp]
def get_openm_ids (Γ : Ctx Term) (cls_idx : Nat) : DsM (List Nat) :=
  if (Γ.is_opent cls_idx)
  then
    let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
    .ok ((ids.takeWhile (Γ.is_openm ·)).reverse)
  else .error ("get_open_ids" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)

-- Get all the instances for a given opent
@[simp]
def get_insts (Γ : Ctx Term) (cls_idx : Nat) : DsM (List (Nat × Term)) := do
  if (Γ.is_opent cls_idx)
  then
    let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
    .ok (ids.foldl (λ acc i =>
    match (Γ d@ i) with
    | .insttype iτ =>
      let (Γ_l, ret_ty) := iτ.to_telescope
      match (ret_ty.neutral_form) with
      | .none => acc
      | .some (h, _) => if h == Γ_l.length + cls_idx then ((i, iτ) :: acc) else acc
    | _ => acc
    ) [])
  else .error ("get_inst_ids" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)

abbrev FunDep := (List Nat) × Nat

def get_fundeps (Γ : Ctx Term) (cls_idx : Nat) : DsM (List FunDep) :=
  if Γ.is_opent cls_idx
  then do
      let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
      let fd_oms := ids.foldl (λ acc i =>
      match (Γ d@ i) with
      | .openm mτ =>
        let (Γ_l, ret_ty) := mτ.to_telescope
        if Option.isSome (is_eq ret_ty)
        then (mτ :: acc) else acc
      | _ => acc
      ) []
      -- each fd_om is of the form ∀αs. F αs -> F αs' -> α ~ α'
      --
      fd_oms.foldlM (λ acc τ => do
        let (tele, _) := τ.to_telescope
        let (tele_tyvars, tele_cls) := tele.partition (·.is_kind)
        if tele_cls.length != 2 then .error "get_fundeps error" else

        let cls1 <- .toDsMq tele_cls[0]? -- F αs
        let cls1 : Term <- .toDsMq cls1.get_type
        let cls2 <- .toDsMq tele_cls[1]? -- F αs'
        let cls2 : Term <- .toDsMq cls2.get_type

        -- TODO: But what if we have a partial fundep?
        let det_idx : Option Nat :=
          match (([S] cls1).neutral_form, cls2.neutral_form) with
          | (Option.some (_, αs), Option.some (_, αs')) =>
              (List.zip αs αs').findIdx (λ (x : ((SpineVariant × Term) × (SpineVariant × Term))) =>
                match x with
                | ((.kind, t1), (.kind, t2)) => if t1 == t2 then false else true
                | _ => false)
            -- .some 0
          | _ => .none

          match det_idx with
          | Option.some determinant =>
            -- TODO: But what if we have a partial fundep?
            let determiners := (Term.shift_helper tele_tyvars.length).filter (λ x => x == determinant)
            if determinant < tele_tyvars.length then .ok ((determiners, determinant) :: acc)
            else .error ("cannot find determinant for class" ++ repr cls_idx ++ " det_idx:" ++ repr det_idx)
          | .none => .error ("cannot find determinant for class" ++ " det_idx:" ++ repr det_idx)
        ) []
  else
  .error ("get_fundeps" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)



def try_type_improvement (Γ : Ctx Term) : Nat -> DsM (List (Term × Term)) := λ i => do
let τ <- .toDsM "try_type_impr" (Γ d@ i).get_type
let Γ_local_tyvars := Γ.tail.takeWhile (·.is_kind)
let local_tyvars := (fresh_vars Γ_local_tyvars.length).reverse.map ([S]·)
match τ.neutral_form with
| .some (τh, τs) => do
  if not (Γ.is_opent τh) then .ok [] else
  -- get all the open method indices
  let openm_ids <- get_openm_ids Γ τh
  -- .ok ((fd_ids.zip fd_ids).map (λ x => (#x.1, #x.2)))
  let (fd_ids, _) := openm_ids.partition (λ x =>
      let f := Γ d@ x
      if f.is_openm then
        match f.get_type with
        | .some τ =>
          let (_, ret_ty) := Term.to_telescope τ;
          Option.isSome (is_eq ret_ty)
        | .none => false
      else false )
  -- .ok ((fd_ids.zip fd_ids).map (λ x => (#x.1, #x.2)))

  -- find all the available instances of the opentype
  let insts <- get_insts Γ τh
  -- .ok ((inst_ids.zip inst_ids).map (λ x => (#x.1, #x.2)))
  -- Extract the type instances

  -- TODO: assuming that I do not have any quantified types.
  -- That would require some more work

  let new_eqs : List (Term × Term) <- insts.foldlM (λ acc x => do
    let (idx, iτ) := x
    let τs := τs.map (·.2)
    -- find the types that this instance type is applied to
    let (Γ_iτ, ret_τ) := iτ.to_telescope
    let (Γ_tyvars, Γ_assms) := Γ_iτ.partition (λ x => x.is_kind)

    -- let (_, ret_τ_τs) <- .toDsM "ret_τ neutral form try_type_improvement" ret_τ.neutral_form
    if Γ_tyvars.length != Γ_assms.length then .error ("quantified instances are not supported for fundeps (yet)")

    let inst_τs : (List Term) := ((Term.shift_helper Γ_assms.length).zip Γ_assms).foldl
      (λ (acc : List Term) (x : Nat × Frame Term) =>
      match x with
      | (si, .type x) =>
        match (is_eq x) with
        -- all (A ~ B) in inst types have first tyvar as β bound, second tyvar the actual type instance
        | .some (_, _, B) => ([P' (si + Γ_tyvars.length)]B) :: acc -- reindex it wrt input Γ
        | _ => acc
      | _ => []) []


    -- instantiate the fd function with the inst_τs
    let fd_terms <- fd_ids.mapM (λ fd_id => do
      let t := Term.mk_ty_apps #fd_id inst_τs
      let fd_τ <- .toDsM "fd_τ get_type" (Γ d@ fd_id).get_type
      let τ <- .toDsM "fd_τ instantiate types" (instantiate_types fd_τ inst_τs)
      .ok (τ, t)
      )

    -- instantiate the fd_terms with the free vars in the context (Γ_tyvars)

    let fd_terms <- fd_terms.mapM (λ x => do
       let t := Term.mk_ty_apps x.2 local_tyvars
       let fd_τ <- .toDsM "fd_τ instantiate types 2" (instantiate_types x.1 local_tyvars)
       .ok (fd_τ, t)
    )

    -- synthesize all the arguments to the fd_open method to get all the equalities
    let fd_terms <- fd_terms.mapM (λ x => do
      let τ := x.1
      let t := x.2
      let (Γ_tele, ret_ty) := τ.to_telescope

      ((Term.shift_helper Γ_tele.length).zip Γ_tele).foldlM (λ acc x => do
        let (τ, t) := acc
        match x with
        | (idx, .type argτ) =>
          let argτ := [P' idx] argτ -- make τ wrt input Γ
          let arg <- .toDsM ("synth_term failed in fd_terms"
                  ++ Std.Format.line ++ repr argτ
                  ++ Std.Format.line ++ repr Γ
                  ++ Std.Format.line ++ repr acc
                  ) (synth_term Γ argτ)
          let τ' <- .toDsM "instantiate types failed in fd_terms" (instantiate_type τ argτ)
          let t' := t `@ arg
          .ok (τ', t')
        | _ => .error ("urk! fd_term not instantiated completely")
      ) (τ, t)

    )

    .ok (fd_terms ++ acc)
    ) []
  .ok (new_eqs)
  -- .ok []

-- No type improvements possible
| _ => .ok []


namespace Algorithm.Test

-- Test for improvements
  def Γ1 : Ctx Term := [
  .type (#12 `@k #6 `@k #0),
  .kind ★,
  .term (#4 -t> #5 -t> #6) (`λ[#4] `λ[#5] #5),
  .inst #8
    (Λ[★]Λ[★]Λ[★]`λ[#12 `@k #2 `@k #1]
      `λ[#13 `@k #3 `@k #1]
      .guard (#5 `@t #4 `@t #3) #1 (
          `λ[(#4 ~[★]~ #8)]
          `λ[(#4 ~[★]~ #9)]
          .guard (#7 `@t #6 `@t #4) #2 (
              `λ[(#6 ~[★]~ #10)]
              `λ[(#5 ~[★]~ #11)]
              (refl! ★ #7) `;
              #2 `;
              (sym! #0)))),
 .insttype (∀[★]∀[★](#1 ~[★]~ #4) -t> (#1 ~[★]~ #5) -t> #12 `@k #3 `@k #2),
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .ctor #2,
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .openm (∀[★]∀[★]∀[★]#3 `@k #2 `@k #1 -t> #4 `@k #3 `@k #1 -t> (#3 ~[★]~ #2)),
 .opent (★ -k> ★ -k> ★)]

 #guard wf_ctx Γ1 == .some ()

 #eval DsM.run (try_type_improvement Γ1 0)

--  #guard (try_type_improvement Γ1 (#12 `@k #6 `@k #0)) == .ok ([(#6 ~[★]~ #0, #11 `@t #6 `@t #0 )])
 #eval infer_type Γ1 (#12 `@t #7 `@t #1 `@t #7 `@ #0)

end Algorithm.Test







def helper1
  (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
  (Γ : Ctx Term)
  (head : HsTerm)
  : DsM (Term × Term)
:=
  match head with
  | .HsAnnotate τh h => do
    let τh' <- compile Γ ★ τh
  -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
    let h' <- compile Γ τh' h
    DsM.ok (h', τh')
  | .HsVar h => do
    let τh' <- DsM.toDsM ("helper1 head" ++ repr head) (Γ d@ h).get_type
    -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
    .ok (#h, τh')
  | t => DsM.error ("helper1 unsupported head" ++ repr t)

def helper2
  (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
  (Γ : Ctx Term)
  : Term × Term -> HsSpineVariant × HsTerm -> DsM (Term × Term)
:= λ acc arg => do
  let (accτ, acc) : Term × Term := acc
  let (τ, res_τ) <- .toDsM ("helper2 " ++ repr accτ) accτ.to_telescope_head
  match τ, arg with
  | .kind k, (.type, arg) => do -- accτ better of of the form ∀[a] b
    let arg' <- compile Γ k arg
    .ok (res_τ β[arg'], acc `@t arg')
  | .type k, (.term, arg) => do -- accτ better of of the form a -> b
    let arg' <- compile Γ k arg
    .ok (res_τ β[arg'], acc `@ arg')
  | _, _ => .error ("heper2" ++ repr τ ++ repr arg)

-- @[simp]
partial def compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , □, `★ => .ok ★

| Γ, □ , .HsCtor2 .arrowk t1 t2 => do
  let t1' <- compile Γ □ t1
  let t2' <- compile Γ □ t2
  .ok (.ctor2 .arrowk t1' t2')

| Γ, κ, .HsCtor2 .appk f a => do
  let (h, sp) <- .toDsMq (HsTerm.split_kind_app (.HsCtor2 .appk f a))
  let τ <- .toDsM ("GetType" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h) ((Γ d@ h).get_type)
  let (κs, κ') <- .toDsMq (Term.split_kind_arrow τ)
  let args' <- List.mapM
    (λ a => compile Γ a.1 a.2)
    (List.zip κs sp)
  .ok (Term.mk_kind_app h args')


| Γ, ★ , .HsBind2 .arrow A B => do
  let A' <- compile Γ ★ A
  let B' <- compile (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .farrow A B => do
  let A' <- compile Γ ★ A
  let B' <- compile (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .all A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.kind A' :: Γ) ★ B
  .ok (.bind2 .all A' B')

| Γ, τ, .HsHole a => do
  let k <- .toDsM ("Wanted τ kind"
           ++ Std.Format.line ++ repr Γ
           ++ Std.Format.line ++ repr τ
            ) (infer_kind Γ τ)
  let a' <- compile Γ k a

  let t <- .toDsM ("synth_term hole"
           ++ Std.Format.line ++ repr Γ
           ++ Std.Format.line ++ repr a')
           (synth_term Γ a')

  -- τ is wanted
  -- a' is what we have/given
  -- the coercion goes form a' ---> τ
  if τ == a'
  then .ok t
  else do
    let η <- .toDsM ("synth_term coercion hole"
             ++ Std.Format.line ++ repr Γ
             ++ Std.Format.line ++ repr (a' -t> [S]τ))
             (synth_term Γ (a' -t> [S]τ))
    .ok (η `@ t)


| Γ, .bind2 .arrow A B, .HsBind2 .lam A' t => do
  let α' <- compile  Γ ★ A'
  if A == α'
  then do
    -- If A is a typeclass/opent and it has some
    -- fundeps associated with it. We can introduce
    -- some type refinements at this point while compiling
    -- the body of the function

    let new_eqs <- try_type_improvement (.type A :: Γ) 0
    let st := [S' new_eqs.length] t
    -- The eqs are wrt Γ so shift them to be wrt type A :: Γ
    let Γ_eqs := ((Term.shift_helper new_eqs.length).zip new_eqs).reverse.map (λ x =>
        let (shift_idx, A, t) := x
        .term ([S' (shift_idx)]A) ([S' (shift_idx)]t))

    let t' <- compile (Γ_eqs ++ .type A :: Γ) ([S' Γ_eqs.length]B) st
    let t' <- .toDsM "mk_lets failed" (t'.mk_lets Γ_eqs)

    .ok (.bind2 .lam A t')
  else .error ("compile lam"
                ++ Std.Format.line ++ (repr (A -t> B))
                ++ Std.Format.line ++ (repr (λ̈[A'] t)))

| Γ, .bind2 .all A B, .HsBind2 .lamt A' t => do
  let α' <- compile Γ □ A'
  if A == α'
  then do
    let t' <- compile (.kind A :: Γ) B t
    .ok (.bind2 .lamt A t')
  else .error ("compile lamt" ++ (repr (∀[A] B)) ++ (repr (Λ̈[A'] t)))

-- guard blah in
-- guard blah in \ . \ .
--   ... : u ~ v


| Γ, τ, .HsLet A t1 t2 => do
  let α <- compile Γ ★ A
  let t1' <- compile Γ α t1
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .ok (.letterm α t1' t2')

| Γ, τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile Γ ★ pτ
  let p' <- compile Γ pτ' p
  let sτ' <- compile Γ ★ sτ
  let s' <- compile Γ sτ' s
  let iτ' <- compile Γ ★ iτ
  let i' <- compile Γ iτ' i
  let t' <- compile Γ τ t
  .ok (.ite p' s' i' t')

| Γ, exp_τ, `#h => do
  let τ <- .toDsM ("get_type" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h)
           ((Γ d@ h).get_type)
  if τ == exp_τ
  then .ok #h
  else do
    let η <- .toDsM ("synth_coercion variable" ++ Std.Format.line ++ repr Γ
                    ++ Std.Format.line ++ repr (τ ~[★]~ exp_τ)
                    ++ Std.Format.line ++ repr h) (synth_coercion Γ τ exp_τ)
    .ok (#h ▹ η)

| Γ, exp_τ, t => do
  let (head, args) <- .toDsM ("no neutral form" ++ repr t) t.neutral_form
  -- Compile Head
  let (h', τh') <- helper1 compile Γ head
  let (τs, res_τh') := τh'.to_telescope

  if args.length > τs.length
  then .error ("compile length mismatch"
                ++ Std.Format.line ++ (repr exp_τ)
                ++ Std.Format.line ++ (repr t))
  else
  -- Compile Args and actual type
    let (actual_τ, t') <- args.foldlM (helper2 compile Γ) (τh', h')
    if exp_τ == actual_τ
    then .ok t'
    else do
      let η <- .toDsM ("synth_coercion spine" ++ repr Γ ++ Std.Format.line ++ repr (actual_τ ~[★]~ exp_τ))
                      (synth_coercion Γ actual_τ exp_τ)
      .ok (t' ▹ η)

-- | _, _, _ => .none
-- decreasing_by repeat sorry
-- all_goals(simp at *)
-- case _ => sorry


namespace Algorithm.Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

    #guard wf_ctx Γ == .some ()

    #guard (compile Γ (∀[★](#6 `@k #0) -t> #1 -t> #2 -t> #10) `#0) == .ok #0
    #guard (compile Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6)) == .ok (#0 `@t #6)
    #guard (compile Γ (#5 `@k #6) (.HsHole (`#5 `•k `#6))) == .ok (#4 `@t #6 `@ (refl! ★ #6))
    #guard (compile Γ (#6 -t> #7 -t> #8) (`#0 `•t `#6 `• (.HsHole (`#5 `•k `#6)))) ==
                  .ok (#0 `@t #6 `@ (#4 `@t #6 `@ (refl! ★ #6)))

end Algorithm.Test

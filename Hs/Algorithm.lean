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

-- @[simp]
unsafe def compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> Option Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , □, `★ => .some ★

| Γ, □ , .HsCtor2 .arrowk t1 t2 => do
  let t1' <- compile Γ □ t1
  let t2' <- compile Γ □ t2
  .some (.ctor2 .arrowk t1' t2')

| Γ, κ, .HsCtor2 .appk f a => do
  let (h, sp) <- HsTerm.split_kind_app (.HsCtor2 .appk f a)
  let τ <- (Γ d@ h).get_type
  let (κs, κ') <- Term.split_kind_arrow τ
  let args' <- List.mapM
    (λ a => compile Γ a.1 a.2)
    (List.zip κs sp)

  .some (Term.mk_kind_app h args')


| Γ, ★ , .HsBind2 .arrow A B => do
  let A' <- compile Γ ★ A
  let B' <- compile (.empty :: Γ) ★ B
  .some (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .farrow A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.empty :: Γ) ★ B
  .some (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .all A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.kind A' :: Γ) ★ B
  .some (.bind2 .all A' B')

-- | Γ, κ , .HsCtor2 .appk A (.HsAnnotate k B) => do
--   let k' <- compile Γ □ k
--   let A' <- compile Γ (k' -k> κ) A
--   let B' <- compile Γ k' B
--   .some (.ctor2 .appk A' B')

| Γ, τ, .HsHole a => do
  let a' <- compile Γ ★ a
  let t <- synth_term Γ a'
  if τ == a'
  then .some t
  else do
    let η <- synth_coercion Γ a' τ
    .some (t ▹ η )


| Γ, .bind2 .arrow A B, .HsBind2 .lam A' t => do
  let α' <- compile  Γ ★ A'
  if A == α'
  then do
    let t' <- compile (.type A :: Γ) B t
    .some (.bind2 .lam A t')
  else .none

| Γ, .bind2 .all A B, .HsBind2 .lamt A' t => do
  let α' <- compile Γ □ A'
  if A == α'
  then do
    let t' <- compile (.kind A :: Γ) B t
    .some (.bind2 .lamt A t')
  else .none

-- guard blah in
-- guard blah in \ . \ .
--   ... : u ~ v


| Γ, τ, .HsLet A t1 t2 => do
  let α <- compile Γ ★ A
  let t1' <- compile Γ α t1
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .some (.letterm α t1' t2')

| Γ, τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile Γ ★ pτ
  let p' <- compile Γ pτ' p
  let sτ' <- compile Γ ★ sτ
  let s' <- compile Γ sτ' s
  let iτ' <- compile Γ ★ iτ
  let i' <- compile Γ iτ' i
  let t' <- compile Γ τ t
  .some (.ite p' s' i' t')

| Γ, exp_τ, `#h => do
  let τ <- (Γ d@ h).get_type
  if τ == exp_τ
  then .some #h
  else do
    let η <- synth_coercion_dummy Γ τ exp_τ
    .some (#h ▹ η)

--
-- f : Eq a => B -> A
-- b : B

-- f (annotate B b)
-- goal type is A

-- (annoate T f) a1 a2 a3

-- (annotate eta (Eq a => B -> C)) ? a1 a2

-- (==) : Eq a => a -> a -> Bool
-- eta : Eq a => a -> a -> Bool
-- eta = \ a. \ b. a == b

| Γ, exp_τ, t => do
  let (head, args) <- t.neutral_form
  -- Compile Head
  let (h', τh') <-
    match head with
    | .HsAnnotate τh h => do
      let τh' <- compile Γ ★ τh
    -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
      let h' <- compile Γ τh' h
      .some (h', τh')

    | .HsVar h => do
      let τh' <- (Γ d@ h).get_type
      -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
      .some (#h, τh')
    | _ => .none
  let (τs, res_τh') := τh'.to_telescope

  if args.length > τs.length then .none
  else
  -- Compile Args and actual type
    let (actual_τ, t') <- args.foldlM (λ acc arg => do
        let (accτ, acc) : Term × Term := acc
        let (τ, res_τ) <- accτ.to_telescope_head
        match τ, arg with
        | .kind k, (.type, arg) => do -- accτ better of of the form ∀[a] b
          let arg' <- compile Γ k arg
          .some (res_τ β[arg'], acc `@t arg')
        | .type k, (.term, arg) => do -- accτ better of of the form a -> b
          let arg' <- compile Γ k arg
          .some (res_τ β[arg'], acc `@ arg')
        | _, _ => .none)
        (τh', h')

    if exp_τ == actual_τ
    then .some t'
    else do
      let η <- synth_coercion_dummy Γ actual_τ exp_τ
      .some (t' ▹ η)
-- | _, _, _ => .none
-- decreasing_by repeat sorry
-- all_goals(simp at *)
-- case _ => sorry


namespace Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

    #guard wf_ctx Γ == .some ()

    #eval (Γ d@ 0)
    #eval! compile Γ (∀[★](#6 `@k #0) -t> #1 -t> #2 -t> #10) `#0
    #eval! compile Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6)
    #eval! compile Γ (#5 `@k #6) (.HsHole (`#5 `•k `#6))
    #eval! compile Γ (#6 -t> #7 -t> #8) (`#0 `•t `#6 `• (.HsHole (`#5 `•k `#6)))


end Test

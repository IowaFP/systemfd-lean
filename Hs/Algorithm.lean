import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm
import Hs.SynthInstance

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


def checkArgsLength (Γ : Ctx Term) (args : List (HsSpineVariant × HsTerm)) (τs : Ctx Term) : DsM Unit := do
  if args.length > τs.length
  then .error ("compile length mismatch"
                ++ Std.Format.line ++ repr args
                ++ Std.Format.line ++ repr τs
                ++ Std.Format.line ++ repr Γ)
  else .ok ()


partial def mb_coerce (Γ : Ctx Term) (t : Term) (exp_τ : Term) (actual_τ : Term) : DsM Term :=
if exp_τ == actual_τ
then .ok t
else do
   let η <- .toDsM ("mb_coerce" ++ repr Γ ++ Std.Format.line ++ repr (actual_τ ~[★]~ exp_τ))
                      (synth_coercion Γ actual_τ exp_τ)
   .ok (t ▹ η)



@[simp]
def split_ty_qtys : Term -> (Ctx Term × Term)
| .bind2 .all k A =>
  let (Γ, r) := split_ty_qtys A
  (.kind k :: Γ, r)
| t => ([], t)

@[simp]
def split_ty_preds (Γ : Ctx Term) : Term -> (Ctx Term × Term)
| .bind2 .arrow p A =>
  let pnf := p.neutral_form
  match pnf with
  | .none => ([], p -t> A)
  | .some (ph, _) =>
    if Γ.is_opent ph then
      let (Γ, r) := split_ty_preds (.type p :: Γ) A
      (.type p :: Γ, r)
    else ([], p -t> A)
| t => ([], t)

@[simp]
def split_tys : Term -> (Ctx Term × Term)
| .bind2 .arrow A B =>
  let (Γ, r) := split_tys B
  (.type A :: Γ, r)
| t => ([], t)


@[simp]
def to_telescope_hm (Γ : Ctx Term) (t : Term) : (Ctx Term × Ctx Term × Ctx Term × Term) :=
  let (qvars, t) := split_ty_qtys t
  let (preds, t) := split_ty_preds (qvars ++ Γ) t
  let (tys, t) := split_tys t
  (qvars, preds, tys, t)

@[simp]
def compile_kind (Γ : Ctx Term) : Term -> HsTerm -> DsM Term
  | □, `★ => .ok ★
  | □, (k1 `-k> k2) => do
    let k1' <- compile_kind Γ □ k1
    let k2' <- compile_kind Γ □ k2
    return k1' -k> k2'
  | τ , t => .error ("comile kind failed" ++ repr τ ++ repr t)

@[simp]
def compile_type (Γ : Ctx Term) : Term -> HsTerm -> DsM Term
  | ★ , .HsBind2 .arrow A B => do
  let A' <- compile_type Γ ★ A
  let B' <- compile_type (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

  | ★ , .HsBind2 .farrow A B => do
  let A' <- compile_type Γ ★ A
  let B' <- compile_type (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

  | ★ , .HsBind2 .all A B => do
  let A' <- compile_kind Γ □ A
  let B' <- compile_type (.kind A' :: Γ) ★ B
  .ok (.bind2 .all A' B')

  | exp_κ, τ => do
    let tnf := τ.neutral_form
    match thfp : tnf with
    | .none => .error ("compile_type neutral form" ++ repr τ)
    | .some (h, sp) =>
      match h with
      | `#h =>
        let τ <- .toDsM ("compile_type get type" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h)
              ((Γ d@ h).get_type)
        let (κs, actual_κ) <- .toDsMq (Term.split_kind_arrow τ)
        if keq : exp_κ == actual_κ && sp.all (λ x => x.1 == .kind) && κs.length == sp.length
        then
          let zz := List.attach (List.zip (List.attach κs) (List.attach sp))
          let args' <- zz.mapM
                    (λ arg =>
                      compile_type Γ arg.val.1 (arg.val.2.val.2))
          .ok (Term.mk_kind_app h args')
        else .error ("compile_type ill kinded" ++ repr τ)
      | _ => .error ("compile_type head" ++ repr h ++ repr sp)
termination_by _ t => t.size
decreasing_by (
any_goals (simp; omega)
case _ =>
  simp at keq; cases keq;
  case _ j1 j2 =>
    let argv := arg.val
    have lem := HsTerm.application_spine_size τ thfp argv.2.val.2;
    simp at lem;
    apply lem argv.2.val.1 argv.2.property;
)

def compile_head
  (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
  (Γ : Ctx Term)
  (head : HsTerm)
  : DsM (Term × Term)
:=
  match head with
  | .HsAnnotate τh h => do
    let τh' <- compile_type Γ ★ τh
  -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
    let h' <- compile Γ τh' h
    DsM.ok (h', τh')
  | .HsVar h => do
    let τh' <- DsM.toDsM ("compile_head head" ++ repr head) (Γ d@ h).get_type
    -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
    .ok (#h, τh')
  | t => DsM.error ("compile_head unsupported head" ++ repr t)

def compile_args
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


partial def compile (Γ : Ctx Term) : (τ : Term) -> (t : HsTerm) -> DsM Term

| τ, .HsHole a => do
  let k <- .toDsM ("Wanted τ kind"
           ++ Std.Format.line ++ repr Γ
           ++ Std.Format.line ++ repr τ
            ) (infer_kind Γ τ)
  let a' <- compile_type Γ k a

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


| .bind2 .arrow A B, .HsBind2 .lam A' t => do
  let α' <- compile_type  Γ ★ A'
  if A == α'
  then do
    -- If A is a typeclass/opent and it has some
    -- fundeps associated with it. We can introduce
    -- some type refinements at this point while compiling
    -- the body of the function

    let new_eqs <- try_type_improvement (.type A :: Γ) 0
    let st := [S' new_eqs.length] t
    let sB := [S' new_eqs.length]B

    -- The eqs are wrt Γ so shift them to be wrt type A :: Γ
    let Γ_eqs := ((Term.shift_helper new_eqs.length).zip new_eqs).reverse.map (λ x =>
        let (shift_idx, A, t) := x
        .term ([S' (shift_idx)]A) ([S' (shift_idx)]t))

    let t' <- compile (Γ_eqs ++ .type A :: Γ) sB st
    let t' <- .toDsM "mk_lets failed" (t'.mk_lets Γ_eqs)
    -- TODO: instead of mk_lets maybe eagerly inline them?

    .ok (`λ[A] t')
  else .error ("compile lam"
                ++ Std.Format.line ++ (repr (A -t> B))
                ++ Std.Format.line ++ (repr (λ̈[A'] t)))

| .bind2 .all A B, .HsBind2 .lamt A' t => do
  let α' <- compile_kind Γ □ A'
  if A == α'
  then do
    let t' <- compile (.kind A :: Γ) B t
    .ok (Λ[A] t')
  else .error ("compile lamt" ++ (repr (∀[A] B)) ++ (repr (Λ̈[A'] t)))

| τ, .HsLet A t1 t2 => do
  let α <- compile_type Γ ★ A
  let t1' <- compile Γ α t1
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .ok (.letterm α t1' t2')

| τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile_type Γ ★ pτ
  let p' <- compile Γ pτ' p
  let sτ' <- compile_type Γ ★ sτ
  let s' <- compile Γ sτ' s
  let iτ' <- compile_type Γ ★ iτ
  let i' <- compile Γ iτ' i
  let t' <- compile Γ τ t
  .ok (.ite p' s' i' t')

| exp_τ, t => do
  let (head, args) <- .toDsM ("no neutral form" ++ repr t) t.neutral_form

  -- Compile Head
  let (h', τh') <- compile_head compile Γ head
  let (τs, _) := τh'.to_telescope

  -- make sure the length of the arguments is fine
  checkArgsLength Γ args τs

  -- Compile Args and actual type
  let (actual_τ, t') <- List.foldlM (compile_args compile Γ) (τh', h') args

  -- coerce if needed and return
  mb_coerce Γ t' exp_τ actual_τ


-- namespace Algorithm.Test
--   def Γ : Ctx Term := [
--     .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
--     .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
--     .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
--     .opent (★ -k> ★),
--     .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
--     .opent (★ -k> ★),
--     .datatype ★ ]

--     #guard wf_ctx Γ == .some ()

--     #guard (compile Γ (∀[★](#6 `@k #0) -t> #1 -t> #2 -t> #10) `#0) == .ok #0
--     #guard (compile Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6)) == .ok (#0 `@t #6)
--     #guard (compile Γ (#5 `@k #6) (.HsHole (`#5 `•k `#6))) == .ok (#4 `@t #6 `@ (refl! ★ #6))
--     #guard (compile Γ (#6 -t> #7 -t> #8) (`#0 `•t `#6 `• (.HsHole (`#5 `•k `#6)))) ==
--                   .ok (#0 `@t #6 `@ (#4 `@t #6 `@ (refl! ★ #6)))

-- end Algorithm.Test

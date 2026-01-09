import Hs.Translator.Types
import SystemFD.Algorithm
import Hs.SynthInstance

@[simp]
def mb_coerce (Γ : Ctx Term) (t : Term) (exp_τ : Term) (actual_τ : Term) : DsM Term :=
if exp_τ == actual_τ
then .ok t
else do
   let η <- .toDsM ("mb_coerce" ++ repr Γ ++ Std.Format.line ++ repr (actual_τ ~[★]~ exp_τ))
                      (synth_coercion Γ actual_τ exp_τ)
   .ok (t ▹ η)

@[simp]
def checkArgsLength (Γ : Ctx Term) (args : List (HsSpineVariant × HsTerm)) (τs : Ctx Term) : DsM Unit := do
  if args.length > τs.length
  then .error ("compile length mismatch"
                ++ Std.Format.line ++ repr args
                ++ Std.Format.line ++ repr τs
                ++ Std.Format.line ++ repr Γ)
  else .ok ()

theorem check_args_length_lemma : checkArgsLength Γ args τs = .ok () -> args.length ≤ τs.length := by
unfold checkArgsLength; simp

@[simp]
def compile_term (Γ : Ctx Term) : (τ : Term) -> (t : HsTerm) -> DsM Term
| τ, .HsHole a => do
  let k <- .toDsM ("Wanted τ kind"
           ++ Std.Format.line ++ repr Γ
           ++ Std.Format.line ++ repr τ
            ) (infer_kind Γ τ)
  let a' <- compile_type Γ k a

  let t <- .toDsM ("synth_term hole"
           ++ Std.Format.line ++ repr Γ
           ++ Std.Format.line ++ repr a')
           (synth_term Γ.length Γ a')

  -- τ is wanted
  -- a' is what we have/given
  -- the coercion goes form a' ---> τ
  if τ == a'
  then .ok t
  else do
    let η <- .toDsM ("synth_term coercion hole"
             ++ Std.Format.line ++ repr Γ
             ++ Std.Format.line ++ repr (a' -t> [S]τ))
             (synth_term Γ.length Γ (a' -t> [S]τ))
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
    let st := [S' new_eqs.length]t
    let sB := [S' new_eqs.length]B

    -- The eqs are wrt Γ so shift them to be wrt type A :: Γ
    let Γ_eqs := ((Term.shift_helper new_eqs.length).zip new_eqs).reverse.map (λ x =>
        let (shift_idx, A, t) := x
        .term ([S' (shift_idx)]A) ([S' (shift_idx)]t))

    let t' <- compile_term (Γ_eqs ++ .type A :: Γ) sB st
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
    let t' <- compile_term (.kind A :: Γ) B t
    .ok (Λ[A] t')
  else .error ("compile lamt" ++ (repr (∀[A] B)) ++ (repr (Λ̈[A'] t)))

| τ, .HsLet A t1 t2 => do
  let α <- compile_type Γ ★ A
  let t1' <- compile_term Γ α t1
  let t2' <- compile_term (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .ok (.letterm α t1' t2')

| τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile_type Γ ★ pτ
  let p' <- compile_term Γ pτ' p
  let sτ' <- compile_type Γ ★ sτ
  let s' <- compile_term Γ sτ' s
  let iτ' <- compile_type Γ ★ iτ
  let i' <- compile_term Γ iτ' i
  let t' <- compile_term Γ τ t
  .ok (.ite p' s' i' t')

| exp_τ, tm => do
  match tnfp : tm.neutral_form with
  | .some (head, args) =>
    let (h' , τh') <- match cmph : head with
    | .HsAnnotate τh h => do
      let τh' <- compile_type Γ ★ τh
      -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
      let h' <- compile_term Γ τh' h
      DsM.ok (h', τh')
    | .HsVar h => do
      let τh' <- DsM.toDsM ("compile_head head" ++ repr head) (Γ d@ h).get_type
      -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
      .ok (#h, τh')
    | t => DsM.error ("compile_head unsupported head" ++ repr t)

    let arg_τs := List.attach args

    let (actual_τ, t') <- arg_τs.foldlM (λ acc a => do
        let prf := a.property
         match arg_h : a.val, acc.1 with
         | (HsSpineVariant.type, arg) , Term.bind2 .all arg_k τ  => do
            let τ' <- compile_type Γ arg_k arg
            return (τ β[τ'], acc.2 `@t τ')
         | (HsSpineVariant.term, arg), .bind2 .arrow arg_τ r_τ  => do
            let arg' <- compile_term Γ arg_τ arg
            return (r_τ β[arg'], acc.2 `@ arg')
         | _, _ => .error ("unsupported arg compile" ++ repr acc ++ repr a.val)) (τh', h')

    mb_coerce Γ t' exp_τ actual_τ

  | .none => .error ("no neutral form" ++ repr tm)
termination_by τ t => t.size
decreasing_by (
any_goals (simp; omega)
case _ =>
  simp_all;
  have lemA := @hs_term_right_shifting_size_no_change new_eqs.length t
  rw[<-lemA]; simp; omega
case _ =>
  have lem := @HsTerm.application_spine_size (head, args) tm tnfp arg
  simp at lem; replace lem := @lem HsSpineVariant.term
  rw[arg_h] at prf;
  replace lem := lem prf
  assumption
case _ =>
  cases cmph;
  have lem : (HsTerm.HsAnnotate τh h).size ≤ tm.size :=
       @HsTerm.application_spine_head_size (.HsAnnotate τh h) args tm tnfp
  simp at lem; omega
)

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


-- def compile_head
--   (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
--   (Γ : Ctx Term)
--   (head : HsTerm)
--   : DsM (Term × Term)
-- :=
--   match head with
--   | .HsAnnotate τh h => do
--     let τh' <- compile_type Γ ★ τh
--   -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
--     let h' <- compile Γ τh' h
--     DsM.ok (h', τh')
--   | .HsVar h => do
--     let τh' <- DsM.toDsM ("compile_head head" ++ repr head) (Γ d@ h).get_type
--     -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
--     .ok (#h, τh')
--   | t => DsM.error ("compile_head unsupported head" ++ repr t)

-- def compile_args
--   (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
--   (Γ : Ctx Term)
--   : Term × Term -> HsSpineVariant × HsTerm -> DsM (Term × Term)
-- := λ acc arg => do
--   let (accτ, acc) : Term × Term := acc
--   let (τ, res_τ) <- .toDsM ("helper2 " ++ repr accτ) accτ.to_telescope_head
--   match τ, arg with
--   | .kind k, (.type, arg) => do -- accτ better of of the form ∀[a] b
--     let arg' <- compile Γ k arg
--     .ok (res_τ β[arg'], acc `@t arg')
--   | .type k, (.term, arg) => do -- accτ better of of the form a -> b
--     let arg' <- compile Γ k arg
--     .ok (res_τ β[arg'], acc `@ arg')
--   | _, _ => .error ("heper2" ++ repr τ ++ repr arg)

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
def compile (Γ : Ctx Term) : (τ : Term) -> (t : HsTerm) -> DsM Term
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

| exp_τ, tm => do
  match tnfp : tm.neutral_form with
  | .some (head, args) =>
    -- have lem1 : head.size < t.size := sorry
    -- have lem2 : ∀ a ∈ args, a.2.size < t.size := sorry
    -- Compile Head

    let (h' , τh') <- match cmph : head with
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

    -- match dhp : compile_head compile Γ head with
    -- | .ok (h', τh') => do
    let (τs, ret_ty) := τh'.to_telescope

      -- make sure the length of the arguments is fine
    match argsh : checkArgsLength Γ args τs with
    | .ok () =>
        have args_τs_length : args.length ≤ τs.length := check_args_length_lemma argsh
        let arg_τs := List.attach (List.zip args τs)
        let args' <- arg_τs.mapM (λ a => do
            let prf := a.property
            match arg_h : a.val with
            | ((HsSpineVariant.type, arg), (.kind τ)) => do
              let arg' <- compile_type Γ τ arg
              return (SpineVariant.type, arg')
            | ((HsSpineVariant.term, arg), (.type τ)) => do
              let arg' <- compile Γ τ arg
              return (SpineVariant.term, arg')
            | _ => .error ("unsupported arg compile" ++ repr a.val)
            )

        let t' := h'.apply_spine args'
        -- let t' <- List.foldlM (λ acc a => do
        --     match a with
        --     | (.type, arg) => return (acc `@t arg)
        --     | (.term, arg) => return (acc `@ arg)
        --     | _ => .error "spine app failed"
        --     ) h' args'

        let remaining_τs := List.drop args.length τs
        let actual_τ <- .toDsM ("mk_arrow failed") (Term.mk_arrow ret_ty remaining_τs)

        mb_coerce Γ t' exp_τ ([P' args.length]actual_τ)
    | .error e => .error e

      -- Compile Args and actual type
      -- match argsh : List.foldlM (compile_args compile Γ) (τh', h') (List.attach args) with
      -- | .ok (actual_τ, t') =>
      -- -- coerce if needed and return

      -- | .error e => .error e
      -- | .error e => .error e
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
  have lem' := HsTerm.zip_contains prf
  replace lem := lem lem'
  assumption
case _ =>
  simp;
  cases cmph;
  have lem : (HsTerm.HsAnnotate τh h).size ≤ tm.size := @HsTerm.application_spine_head_size (.HsAnnotate τh h) args tm tnfp
  simp at lem; omega
)


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

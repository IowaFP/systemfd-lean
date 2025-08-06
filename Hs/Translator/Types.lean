import Hs.Translator.Kinds

set_option linter.unusedVariables false

@[simp]
def compile_type_meh (Γ : Ctx Term) : Term -> HsTerm -> DsM Term
  -- A → B
  | ★ , .HsBind2 .arrow A B => do
  let A' <- compile_type_meh Γ ★ A
  let B' <- compile_type_meh (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

  -- A ⇒ B
  | ★ , .HsBind2 .farrow A B => do
  let A' <- compile_type_meh Γ ★ A
  let B' <- compile_type_meh (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

  -- ∀[A] B
  | ★ , .HsBind2 .all A B => do
  let A' <- compile_kind Γ □ A
  let B' <- compile_type_meh (.kind A' :: Γ) ★ B
  .ok (.bind2 .all A' B')

  -- A ⬝ B ⬝ D .. (List α etc.)
  | exp_κ, τ => do
    match tnfp : τ.neutral_form with
    | .none => .error ("compile_type_meh neutral form" ++ repr τ)
    -- A [B, C, ..]
    | .some (h, sp) =>
      match h with
      | `#h =>
        let τ <- .toDsM ("compile_type_meh get type" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h)
              ((Γ d@ h).get_type)

        -- split the head kind arrow
        -- A : k1 -> k2 -> ... -> k_ret
        let (κs, actual_κ) <- .toDsMq (Term.split_kind_arrow τ)

        -- make sure the lengths match up
        if exp_κ == actual_κ && sp.all (λ x => x.1 == .kind) && κs.length == sp.length
        then
          -- compile each type with the expected kind
          -- [(B : k1), (C : K2) ...]
          let args' <- (κs.zip sp).mapM
                    (λ arg =>
                      compile_type_meh Γ arg.1 (arg.2.2))
          .ok (Term.mk_kind_app h args')
        else .error ("compile_type_meh ill kinded" ++ repr τ)
      | _ => .error ("compile_type_meh head" ++ repr h ++ repr sp)
termination_by _ t => t.size
decreasing_by (
any_goals (simp; omega)
· sorry -- where does arg come from? :(
)



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
    match tnfp : τ.neutral_form with
    | .none => .error ("compile_type neutral form" ++ repr τ)
    | .some (h, sp) =>
      match h with
      | `#h =>
        let k <- .toDsM ("compile_type get type" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h)
              ((Γ d@ h).get_type)
        match spk : Term.split_kind_arrow k with
        | .none => .error ("no split arrow kind" ++ repr k)
        | .some (κs, actual_κ) => do
          have lem : Term.mk_kind_arrow actual_κ κs = k := by
            sorry
          if exp_κ == actual_κ && sp.all (λ x => x.1 == .kind) && κs.length == sp.length
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
· let argv := arg.val
  have lem := HsTerm.application_spine_size τ tnfp argv.2.val.2;
  simp at lem;
  apply lem argv.2.val.1 argv.2.property;
)

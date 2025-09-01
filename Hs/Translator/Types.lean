import Hs.Translator.Kinds

set_option linter.unusedVariables false

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
        let k <- .toDsM ("compile_type get type" ++ Std.Format.line ++ repr Γ
                        ++ Std.Format.line ++ repr h)
                 ((Γ d@ h).get_type)
        match spk : Term.split_kind_arrow k with
        | .none => .error ("no split arrow kind" ++ repr k)
        | .some (κs, actual_κ) => do
          if exp_κ == actual_κ && sp.all (λ x => x.1 == .kind) && κs.length == sp.length
          then
            let zz := List.attach (List.zip (List.attach κs) (List.attach sp))
            let args' <- zz.mapM
                      (λ arg => if arg.val.2.val.1 == .kind then
                        have lem := arg.property
                        compile_type Γ arg.val.1 (arg.val.2.val.2)
                        else .error ("compile_type ill kinded ty arg" ++ repr arg.val))
            .ok (Term.mk_kind_app_rev #h args'.reverse)
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

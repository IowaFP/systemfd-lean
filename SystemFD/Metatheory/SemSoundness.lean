import SystemFD.Term
import SystemFD.Term.Subexpression
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Confluence

def saturated : Ctx Term -> Term -> Prop := sorry

-- change Term.subexpr to Term.contains_variant decidable predicate

inductive WDVal : Ctx Term -> Term -> Prop where
|  WDVal :
     Val Γ t ->
     ¬ (Term.Subexpr `0 t) ->
     ∀ M N, ¬ (Term.Subexpr (M ⊕ N) t) ->
     ∀ M N P, ¬ (Term.Subexpr (.guard M P N) t) ->
     (∀ x, Term.Subexpr #x t -> Γ.is_openm x -> saturated Γ #x) ->
     WDVal Γ t


inductive WDTerm : Ctx Term -> Term -> Prop where
| WDBase :
    (∃ v, (M ⟨ Γ ⟩⟶⋆ v) ∧  WDVal Γ v) ->
    WDTerm Γ M
| WDChoice1 :
   WDTerm Γ M ->
   (N ⟨ Γ ⟩⟶⋆ `0) ->
   WDTerm Γ (M ⊕ N)
| WDChoice2 :
   WDTerm Γ N ->
   (M ⟨ Γ ⟩⟶⋆ `0) ->
   WDTerm Γ (M ⊕ N)

-- chain
theorem sanity :
  WDTerm Γ M ->
  ∃ v, (M ⟨ Γ ⟩⟶⋆ v) ∧ WDVal Γ v := by
intro h;
induction h
assumption
case _ M N h1 h2 ih =>
  cases ih; case _ v ih =>
  cases ih; case _ ih1 ih2 =>
  have lem : (M ⊕ N) ⟨ Γ ⟩⟶⋆ (v ⊕ `0) := by
    apply reds_choice_parallel ih1 h2
  have lem2 : (v ⊕ `0) ⟨ Γ ⟩⟶⋆ v := by apply RedStar.step; (apply RedStar.refl); constructor
  exists v
  constructor
  apply reds_trans lem lem2
  assumption

case _ N M h1 h2 ih =>
  cases ih; case _ v ih =>
  cases ih; case _ ih1 ih2 =>
  have lem : (M ⊕ N) ⟨ Γ ⟩⟶⋆ (`0 ⊕ v) := by
    apply reds_choice_parallel h2 ih1
  have lem2 : (`0 ⊕ v) ⟨ Γ ⟩⟶⋆ v := by apply RedStar.step; (apply RedStar.refl); constructor
  exists v
  constructor
  apply reds_trans lem lem2
  assumption

import SystemFD.Term
import SystemFD.Term.Subexpression
import SystemFD.Term.Variant
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Confluence

def saturated : Ctx Term -> Term -> Prop := sorry

-- TODO: Change Term.subexpr to Term.contains_variant decidable predicate

inductive WDVal (Γ : Ctx Term) : Term -> Prop where
|  WDVal :
     -- Val Γ t -> -- what if the term is loopy loopy?
     ¬ (Term.Subexpr `0 t) ->
     ∀ M N, ¬ (Term.Subexpr (M ⊕ N) t) ->
     ∀ M N P, ¬ (Term.Subexpr (.guard M P N) t) ->
     (∀ x, Term.Subexpr #x t -> Γ.is_openm x -> saturated Γ #x) ->
     WDVal Γ t


inductive WDVal' (Γ : Ctx Term) : Term -> Prop where
|  WDVal' :
     ¬ (ContainsVariant (Ctx.variants Γ) [.zero, .guard, .ctor2 .choice] t) ->
     (∀ x, Term.Subexpr #x t -> Γ.is_openm x -> saturated Γ #x) ->
     -- cannot use ContainsVariant (Ctx.variants Γ) [.var .opent] becuase i want to imply that it is saturated.
     WDVal' Γ t


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

-- Next step:
-- 1. What does saturation mean?
-- a. Semantically
--    x is saturated iff
--    ∀ τ e, x is open in Γ ->
--    WDValue Γ e ->
--    x[τ]e is of ground type ->
--    x[τ]e -->* ∃ v. WDVal Γ v

-- b. Syntactically
-- c. Syntactic saturation => semantic saturation


-- 2. Syntactic Weakly deterministic Term => Semantic Weakly Deterministic Term
-- Way 1: Syntactic WD Term to use Semantic saturation
-- And then try proving 2.

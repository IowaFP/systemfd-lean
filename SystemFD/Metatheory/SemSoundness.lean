import SystemFD.Term
import SystemFD.Term.Subexpression
import SystemFD.Term.Variant
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Confluence


def saturated : Ctx Term -> Nat -> Prop := sorry
-- TODO: Change Term.subexpr to Term.contains_variant decidable predicate

inductive WDVal (Γ : Ctx Term) : Term -> Prop where
|  WDVal :
     -- Val Γ t -> -- what if the term is loopy loopy?
     ¬ (Term.Subexpr `0 t) ->
     ∀ M N, ¬ (Term.Subexpr (M ⊕ N) t) ->
     ∀ M N P, ¬ (Term.Subexpr (.guard M P N) t) ->
     (∀ x, Term.Subexpr #x t -> Γ.is_openm x -> saturated Γ x) ->
     WDVal Γ t

namespace Term
def mk_ty_tm_app (t : Term) (τs : List Term) (es : List Term) := (t.mk_ty_apps τs).mk_apps es
def GroundTy (Γ : Ctx Term) (t : Term) : Prop := sorry
end Term


-- Semantic Characterization of a Weakly Deterministic Value
inductive SemWDVal (Γ : Ctx Term) : Term ->  Prop where
| SemWDVal :
    ¬ (ContainsVariant (Ctx.variants Γ) [.zero, .guard, .ctor2 .choice] t) ->
    (∀ x : Nat, Term.Subexpr #x t -> Γ.is_openm x ->
    (∀ τs es,
        (∀ e ∈ es, WDVal Γ e) ->
        (∃ σ, Γ ⊢ (#x).mk_ty_tm_app τs es : σ ∧ σ.GroundTy Γ) ->
        (¬ ((#x).mk_ty_tm_app τs es) ⟨ Γ ⟩⟶⋆ `0))) ->
    (∃ v, t ⟨ Γ ⟩⟶⋆ v ∧ Val Γ v) ->
    SemWDVal Γ t


-- a. Semantically
--    x is saturated iff
--    ∀ τ e, x is open in Γ ->
--    WDVal Γ e ->
--    x[τ]e is of ground type ->
--    ¬ (x[τ]e ⟶★ `0)
inductive SemSat (Γ : Ctx Term) : Term -> Prop where
| Sat :
  t = #x ->
  Γ.is_openm x ->
  (∀ τs es,
      (∀ e ∈ es, SemWDVal Γ e) ->
      (∃ σ, Γ ⊢ (#x).mk_ty_tm_app τs es : σ ∧ σ.GroundTy Γ) ->
      (¬ ((#x).mk_ty_tm_app τs es) ⟨ Γ ⟩⟶⋆ `0)) ->
  SemSat Γ t


inductive SemWDTerm (Γ : Ctx Term) : Term -> Prop where
| WDBase :
    (∃ v, (M ⟨ Γ ⟩⟶⋆ v) ∧  Val Γ v) ->
    SemWDTerm Γ M
| WDChoice1 :
   SemWDTerm Γ M ->
   (N ⟨ Γ ⟩⟶⋆ `0) ->
   SemWDTerm Γ (M ⊕ N)
| WDChoice2 :
   SemWDTerm Γ N ->
   (M ⟨ Γ ⟩⟶⋆ `0) ->
   SemWDTerm Γ (M ⊕ N)

-- chain
theorem sanity :
  SemWDTerm Γ M ->
  ∃ v, (M ⟨ Γ ⟩⟶⋆ v) ∧ Val Γ v := by
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
--    WDVal Γ e ->
--    x[τ]e is of ground type ->
--    x[τ]e -->* ∃ v. WDVal Γ v

-- b. Syntactically
--    AI: We don't have a syntactic characterization yet, maybe we never need it for our purposes.
--    After all, when a programmer uses an overloaded operator, there is no indication that
--    that function will actually be fine at runtime syntactically. It is only when the typechecker
--    works on it (does some typed semantic analysis) is when it can generate an instance to fill in
--    that decides what the behavior of the overloaded function is. Open term variables in our case
--    _are_ the  overloaded functions

-- c. Syntactic saturation => semantic saturation


-- 2. Syntactic Weakly deterministic Term => Semantic Weakly Deterministic Term
-- Way 1: Syntactic WD Term to use Semantic saturation
-- And then try proving 2.

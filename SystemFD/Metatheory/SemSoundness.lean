import SystemFD.Term
import SystemFD.Term.Subexpression
import SystemFD.Term.Variant
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Confluence


@[simp]
def ShallowlyDeterm : Term -> Prop
| .zero => false
| .ctor2 .choice _ _ => false
| _ => true


-- Shalowly Deterministic Value is a value which also shallowly deterministic
@[simp]
abbrev SDVal (Γ : Ctx Term) (t: Term) := Val Γ t ∧ ShallowlyDeterm t

 -- where
-- |  SDVal :
--     Val Γ t ->
--     ShallowlyDeterm t ->
--     -- ¬ (ContainsVariant (Ctx.variants Γ) [.zero, .guard, .ctor2 .choice] t) ->
--     -- (∀ x, Term.Subexpr #x t -> Γ.is_openm x -> saturated Γ x) ->
--     SDVal Γ t


namespace Term

def mk_ty_tm_app (t : Term) (τs : List Term) (es : List Term) := (t.mk_ty_apps τs).mk_apps es

-- Ground Types are the ones that are not lambda bound
def GroundTy (Γ : Ctx Term) (t : Term) : Bool :=
  sorry

end Term



-- a. Semantically
--    x is saturated iff
--    ∀ τ e, x is open in Γ ->
--    Val Γ e ->
--    x[τ]e is of ground type ->
--    (∃ v, x[τ]e ⟶★ v ∧ SemWDVal Γ v)
@[simp]
abbrev Sat (Γ : Ctx Term) (x : Nat):  Prop :=
  Γ.is_openm x ∧
  (∀ τs es,
      (∀ e ∈ es, SDVal Γ e) ->
      (∃ σ, Γ ⊢ (#x).mk_ty_tm_app τs es : σ ∧ σ.GroundTy Γ) ->
      (∃ v, ((#x).mk_ty_tm_app τs es) ⟨ Γ ⟩⟶⋆ v ∧ SDVal Γ v))

@[simp]
abbrev SatCtx (Γ : Ctx Term) : Prop := ∀ x, Γ.is_openm x -> Sat Γ x -- sorry

-- TODO: Change Term.subexpr to Term.contains_variant decidable predicate

-- Question: Is the term (λ x. `0) a value, is it weakly deterministic?
-- Claim: WD is a property of arbitrary terms.
-- We have normal forms:
-- Its shallowly determistic value if it doesn't have `0 or ⊕ at the head
--   So, (λ x. `0) is a shallowly deterministic value.
--   but  (`0  ⊕ `0) is not a shallowly deterministic value.

-- Weak Determinism is how we handle open methods
-- this is where guards come in.
-- in any context evaluation C, t is weakly deterministic
-- if C[t] -->* doesn't reduce to `0 or ⊕ i.e. it is shallowly deterministic value.

-- "Shallowness": Terms that we know reduce to `0 (or not) in "one step"
-- Reductions do not preserve shallowness

-- Semantic Characterization of a Weakly Deterministic Value
inductive SemWDVal (Wf : Term -> Prop) (Γ : Ctx Term) : Term ->  Prop where
| SemWDVal :
    ¬ (ContainsVariant (Ctx.variants Γ) [.zero, .guard, .ctor2 .choice] t) ->
    -- Complaint: this syntactic not semantic
    -- (∀ x : Nat, Term.Subexpr #x t -> Γ.is_openm x -> (SemSat P Γ #x)) ->
    -- (∃ v, t ⟨ Γ ⟩⟶⋆ v ∧ SemWDVal Wf Γ v) ->
    SatCtx Γ ->
    Wf t ->
    SemWDVal Wf Γ t

-- IDEA1: fix this by marmaduking it

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

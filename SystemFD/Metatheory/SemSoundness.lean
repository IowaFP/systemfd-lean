import SystemFD.Term
import SystemFD.Term.Subexpression
import SystemFD.Term.Variant
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Confluence
import SystemFD.Metatheory.Progress
import SystemFD.Metatheory.Preservation

set_option maxHeartbeats 500000

/-

Goal
----

We want to have a syntactic property P on terms of SystemFD
(possibly indexed over types and context)
st. the following holds for it:

   P τ t ⇒
   ∃ n, (t ⟶⋆ n) ∧
        (Val Γ n ∧ n is confusion free)
        ∨ ( does not have a normal form)

The context Γ has to bear some responsibility for the term to be confusion free,
as the · ⟶⋆ · relation is dependent on Γ for instantiating open methods. We call this
property saturation. Intuitively, the saturation property enforces that the
(well typed) open method call instantiations cannot cause confusion.

To explicitly encode this property in our formalization:

   SatCtx Γ ∧ P τ Γ t ⇒
   ∃ n, (t ⟨Γ⟩⟶⋆ n) ∧
        (Val Γ n ∧ n is confusion free)
         ∨ n does not have a normal form


Confusion Free (or (Weakly) Determined):
---------------

Idea 1:

Determined Γ τ t

A (well typed) term, t,
1. t does not contain `0 or ⊕ or guards (at the head)
2. open methods are fine but they need to be fully applied -- enforced by typing?


Idea 2:
DeterminedTyping Γ t τ

Deeply checked  Idea 1. check that t does not contain `0, ⊕ etc only at the head but for all subterms of t

theorem : NoConfusion Γ → Closed Γ → DetermindedTyping Γ t τ
          Val Γ t  ∨ (∃ t', t ⟶+ t' ∧ DetermindedTyping Γ t' τ)

m [τs] ds : σ

NoConfusion Γ

    ∀ τs ds,
      (τs are ground, ds are DeterminedTyping Γ σ d, σ is ground)
    ∃ i, Γ d@ i = .inst #m t ∧ t [τs] ds - ̸⟶⋆ `0 ∧
    ∀ k, k ≠ i ∧  Γ d@ k = .inst #m t' ∧ t' [τs] ds ⟶⋆ `0

Captures: Saturation.
1. Instance existence --> no `0
2. Instance uniqueness --> no ⊕


Equivalent to:
∀ m [τs] ds : σ ⟶+ n, DeterminedTyping Γ n σ


-/

namespace Term

def mk_ty_tm_app (t : Term) (τs : List Term) (es : List Term) := (t.mk_ty_apps τs).mk_apps es
notation:70 t:170 "⬝[" τs:170 "]⬝" es:170 "⬝" => mk_ty_tm_app t τs es

-- Ground Types are the ones that are not lambda bound
-- Int, Bool, Int → Bool, Maybe, Maybe Int are all ground types
-- a → Int, Maybe a are not ground types
def groundTy (Γ : Ctx Term) : Term -> Bool
| #x => Γ.is_datatype x || Γ.is_opent x
| (τ1 -t> τ2) => groundTy Γ τ1 && groundTy (.empty :: Γ) τ2
| τ1 `@k τ2 => groundTy Γ τ1 && groundTy  Γ τ2
| _ => false

end Term

namespace Ctx

end Ctx

@[simp]
abbrev NoConfusion (Γ : Ctx Term) (t : Term) : Prop := ¬ contains_variant Γ.variants [.zero, .guard, .ctor2 .choice] t


@[simp]
abbrev Confusion (Γ : Ctx Term) (t : Term) : Prop := contains_variant Γ.variants [.zero, .guard, .ctor2 .choice] t

theorem partition_confusion {Γ : Ctx Term}  {t : Term} : NoConfusion Γ t <-> ¬ Confusion Γ t :=
 by simp



@[simp]
abbrev NoConfusionWellTyped (Γ : Ctx Term) (τ t: Term) : Prop :=
  Γ ⊢ t : τ ∧  NoConfusion Γ t


namespace Ctx

@[simp]
-- A closed context is a context where there are only pure declarations and no let, lambda bound terms
abbrev Closed (Γ : Ctx Term) : Prop :=
  ⊢ Γ ∧  ∀ (x : Nat), (Γ d@ x).is_stable_red

@[simp]
abbrev NoConfusionCtx Γ := ∀ x, Γ.is_openm x -> ∀ τs ds : List Term, ∀ σ : Term, (Γ ⊢ ((#x) ⬝[τs]⬝ ds ⬝) : σ) ∧
  (∀ τ ∈ τs, τ.groundTy Γ) ∧
  (∀ d ∈ ds, ∃ κ, Γ ⊢ d : κ ∧ κ.groundTy Γ ∧ NoConfusionWellTyped Γ κ d) ∧
  ∃ n, ((#x) ⬝[τs]⬝ ds ⬝) ⟨Γ⟩⟶⋆ n ∧ NoConfusionWellTyped Γ σ n

@[simp]
abbrev NoConfusionClosedCtx Γ := NoConfusionCtx Γ ∧ Closed Γ
end Ctx


-- A direct proof of this lemma obviously fails
theorem NoConfusionProgressFail Γ σ t:
  Γ.NoConfusionCtx -> Γ.Closed -> NoConfusionWellTyped Γ σ t ->
  Val Γ t ∨
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ NoConfusionWellTyped Γ σ t') := by
intro h1 h2 h3
simp at h3; cases h3; case _ wt noc =>
have no_var : (∀ x, ¬ Γ.is_type x) := by simp at h2; cases h2; case _ h2 =>
    intro x; replace h2 := h2 x; intro h3; unfold Ctx.is_type at h3;
    replace h3 := type_indexing_exists h3; cases h3; case _ h3 =>
    rw[h3] at h2; unfold Frame.is_stable_red at h2; simp at h2
have lem_p := progress no_var wt
cases lem_p
case _ => constructor; assumption
case _ lem_p =>
  cases lem_p
  case _ h =>
    cases h; case _ t' r =>
    apply Or.inr;
    have lem_pres := preservation wt (RedStar.step RedStar.refl r)
    have lem_prog := progress no_var lem_pres
    cases lem_prog
    case _ h =>
      exists t'
      constructor
      · constructor; constructor; assumption
      · sorry
  -- Have : Γ ⊢ t ⟶ t' : σ. t' is value.
  -- Show: t' has no confusion
  -- we know that NoConfusionWellTyped property is not directly preserved over reduction relation
    case _ h =>
      cases h;
      case _ h => sorry
      case _ h => exfalso; sorry
  case _ e => exfalso; rw[e] at noc; simp at noc


-- Attempt 1: Generalize NoConfusion of terms indexed by its type
-- This is very similar to the Strong Normalization Predicate (indexed by types) for terms

inductive SemNoConfusion (Γ : Ctx Term) : Term -> Term -> Prop
| AppTy :
  Γ.NoConfusionClosedCtx ->
  τ = Term.mk_kind_apps #x τs ->
  NoConfusionWellTyped Γ τ t ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ NoConfusionWellTyped Γ τ t') ->
  SemNoConfusion Γ τ t
| ArrowTy :
  Γ.NoConfusionClosedCtx ->
  NoConfusionWellTyped Γ (τ1 -t> τ2) f ->
  ∀ e, SemNoConfusion Γ τ1 e ->
  σ' = τ2 β[e] ->
  SemNoConfusion Γ σ' (f `@ e)
| AllTy :
  Γ.NoConfusionClosedCtx ->
  NoConfusionWellTyped Γ (∀[K] σ) f ->
  ∀ τ, Γ ⊢ τ : K ->
  σ' = σ β[τ] ->
  SemNoConfusion Γ σ' (f `@t τ)
| EqTy :
  Γ.NoConfusionClosedCtx ->
  ∀ τ1 τ2, Γ ⊢ τ1 : K -> Γ ⊢ τ2 : K ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ NoConfusionWellTyped Γ (τ1 ~[K]~ τ2) t') ->
  SemNoConfusion Γ (τ1 ~[K]~ τ2) t


theorem NoConfusionProgressFail2 :
  SemNoConfusion Γ σ t ->
  Val Γ t ∨
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ NoConfusionWellTyped Γ σ t') := by
intro h
induction h
case _ => apply Or.inr; assumption
case _ ih =>
  apply Or.inr
  cases ih
  case _ f _ _ j1 e j2 _ ih =>
    simp at j1;
    cases j1; case _ j1 _ =>
    have no_var : ∀ x, ¬ Γ.is_type x := sorry
    have lem_prog := progress no_var j1
    cases lem_prog;
    case _ h =>
      have f_shape := canonical_lambda j1; simp at f_shape;
      replace f_shape := f_shape h j1;


      sorry
    case _ => sorry
  case _ ih =>
    cases ih; case _ f _ _ _ _ _ _ e' ih =>
    cases ih
    exists (f `@ e')
    constructor
    sorry
    case _ h1 _ _ _ _ h2 =>
      simp at h1; cases h1;
      simp at h2; cases h2;
      case _ j1 _ j2 _ =>
      simp; constructor
      · apply Judgment.app; assumption; assumption; sorry -- -t> bullshit
      · constructor; assumption; assumption

case _ => sorry
case _ => apply Or.inr; assumption


-- Need to now show stability over substitutions


/-

is confusion free if for all term contexts C[⬝], and saturated context Γ
C[t] ⟨Γ⟩ ⟶⋆ n s.t. n is a value and n does not contain open methods or `0 or ⊕ or guards

Its definitely not the case that any C[⬝] would do.  Why?
C[⬝] itself can easily induce confusion:
if C[⬝] = 3 ⊕ ⬝ then any confusion free term results in confusion

Idea:
Apply some restriction on C[⬝].
A term context C[⬝] is confusion free if it does not contain open methods, `0, ⊕ or guards
The key observation is that confusion can be induced by only these 4 constructs.


Take 2: A term is confusion free if in any confusion free term context  C[⬝], and a saturated context Γ
C[t] ⟨Γ⟩ ⟶⋆ n s.t. n is a value (or it loops indefinitely) and n does not
contain open methods or `0 or ⊕ or guards


Maybe what we need is a measure for confusion for term contexts.






Context Saturation:
-------------------
Intuitively, a context Γ is saturated
If for any open method in the context, there is only one instance that does not make the term vanish.

Suppose `m` is the open method. with type ∀ τs. Qs ⇒ τ'
now, consider all possible (well typed applications) of this open method.
WLOG, `m [τs] ds` such that Γ ⊢ d : Q[α ↦ τ], Γ ⊢ m [τs] ds : τ'[α ↦ τ]

now, `m` will have some associated instantiations I_j in the context of the form (Λ αs .guards ... )
so `m [τs] ds` ⟶ (I_1 ⊕ I_2 ⊕ .. I_n) [τs] ds ⟶⋆ (I_1 [τs] ds) ⊕ (I_2 [τs] ds) ⊕ ... ⊕ (I_n [τs] ds)

Now we want saturation property to capture the idea only one of these I_j survives.

Take 1:

    ∀ τs ds,
      (τs are ground, ds are confusion free)
    ∃ i, Γ d@ i = .inst #m t ∧ t [τs] ds - ̸⟶⋆ `0 ∧
    ∀ k, k ≠ i ∧  Γ d@ k = .inst #m t' ∧ t' [τs] ds ⟶⋆ `0

but our saturation property is too strict! ds shouldn't be confusion free, they can
very well contain calls to open methods. This is where related inputs go to related outputs
idea gets used (I think). ds should satisfy the original goal property P from above.

Option: Let P be collection of terms that contains no guards, `0, ⊕. (open methods are okay)
This seems to have some merit. It is a syntactic check and with context saturation ensuring no confusion

Take 2:

    ∀ τs ds,
      (τs are ground, ds satisfy property P)
    ∃ i, Γ d@ i = .inst #m t ∧ t [τs] ds - ̸⟶⋆ `0 ∧
    ∀ k, k ≠ i,  Γ d@ k = .inst #m t' → (t' [τs] ds ⟶⋆ `0)

-/



namespace TermCtx


end TermCtx


-- shallowly confusion free is a term that does not have a `0 or ⊕ at its head
@[simp]
abbrev ShallowlyConfusionFree (Γ : Ctx Term) : Term -> Prop
| .zero => false
| .ctor2 .choice _ _ => false
| t => Term.isTerm Γ t


-- Shalowly confusion free value is a value which also shallowly confusion free
--   So, (λ x. `0) is a shallowly confusion free value.
--   but  (`0  ⊕ `0) is not a shallowly confusion free value.
@[simp]
abbrev SCFVal (Γ : Ctx Term) (t: Term) := Val Γ t ∧ ShallowlyConfusionFree Γ t

@[simp]
abbrev CanCauseConfusion (Γ : Ctx Term) (t: Term) : Bool :=
  Term.isTerm Γ t ∧
  contains_variant Γ.variants [.var .openm, .zero, .guard, .ctor2 .choice] t


-- a. Semantically,
--    x is saturated iff
--    ∀ τ e, x is open in Γ ->
--    Val Γ e ->
--    x[τ]e is of ground type ->
--    (∃ v, x[τ]e ⟶★ v ∧ Shallowly Confusion Free Γ v)
@[simp]
abbrev Sat (Wf : Ctx Term -> Term -> Prop)(Γ : Ctx Term) (x : Nat):  Prop :=
  ⊢ Γ ∧
  Γ.is_openm x ->
  (∀ τs es σ,
      (∀ τ ∈ τs, τ.groundTy Γ) ->
      (∀ e ∈ es, Wf Γ e) ->
      (Γ ⊢ (#x ⬝[ τs ]⬝ es ⬝) : σ ∧ σ.groundTy Γ ∧ ∃ k, Γ ⊢ σ : k ∧ Γ ⊢ k : □) ->
      (∃ v, (#x ⬝[ τs ]⬝ es ⬝) ⟨ Γ ⟩⟶⋆ v ∧ Wf Γ v))

@[simp]
-- if the variable is not an open thingy then it is automatically saturated
abbrev SatCtx (Wf : Ctx Term -> Term -> Prop) (Γ : Ctx Term) : Prop := ∀ x, Γ.is_openm x -> Sat Wf Γ x

-- Question: Is the term (λ x. `0) a value, but applying it to anything will make it vanish
-- Weak Determinism is how we handle open methods
-- this is where guards come in.
-- in any context evaluation C, t is weakly deterministic
-- if C[t] -->* doesn't reduce to `0 or ⊕ i.e. it is shallowly deterministic value.

-- "Shallowness": Terms that we know reduce to `0 (or not) in "one step"
-- Reductions do not preserve shallowness

-- Semantic Characterization of a Weakly Deterministic Value
@[simp]
abbrev CFVal (Wf : Term -> Prop) (t : Term): Prop := ∀ Γ,
    -- ¬ (ContainsVariant (Ctx.variants Γ) [.zero, .guard, .ctor2 .choice] t) ∧
    -- Complaint: this is syntactic not semantic
    -- (∀ x : Nat, Term.Subexpr #x t -> Γ.is_openm x -> (SemSat P Γ #x)) ->
    -- (∃ v, t ⟨ Γ ⟩⟶⋆ v ∧ CFVal Wf Γ v) ->
    Γ.Closed ->
    SatCtx ShallowlyConfusionFree Γ ->
    Val Γ t ->
    Wf t


inductive CFTerm (Wf : Term -> Prop) (Γ : Ctx Term) : Term -> Prop where
| WDBase :
    Wf M ->
    CFTerm Wf Γ M
| WDChoice1 :
   CFTerm Wf Γ M ->
   (N ⟨ Γ ⟩⟶⋆ `0) ->
   CFTerm Wf Γ (M ⊕ N)
| WDChoice2 :
   CFTerm Wf Γ N ->
   (M ⟨ Γ ⟩⟶⋆ `0) ->
   CFTerm Wf Γ (M ⊕ N)

-- chain
theorem sanity :
  CFTerm (λ M => ∃ v, (M ⟨ Γ ⟩⟶⋆ v) ∧ Val Γ v) Γ M ->
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

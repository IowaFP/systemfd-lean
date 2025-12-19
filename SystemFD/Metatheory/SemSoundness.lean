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
def noOpenType (Γ : Ctx Term) : Term -> Bool
| #x => ¬ Γ.is_openm x
| (τ -t> τ') => noOpenType Γ τ ∧ noOpenType (.type τ :: Γ) τ'
| ∀[K] τ => noOpenType (.kind K :: Γ) τ
| τ `@k τ' => noOpenType Γ τ ∧ noOpenType Γ τ'
| _ => false

@[simp]
abbrev Determined (Γ : Ctx Term) (t : Term) : Prop :=
  (¬ contains_variant Γ.variants [.zero, .guard, .ctor2 .choice] t)


@[simp]
abbrev NeutralFormSpineType : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , τ) => ∀ x, ∀sp, t.neutral_form = .some (x, sp) -> (∃ T, .some T = (Γ d@ x).get_type ∧ ∃ τ' , SpineType Γ sp τ' T)
| .wf => λ _ => λ _ => true

-- Spine type collects prefixes
-- Need to have some connection between the type elements of the spine and the original type
-- Try to repurpose SpineType here
theorem neutral_form_spine_type :
  Judgment v Γ ix ->
  NeutralFormSpineType v Γ ix
   := by
intro j; induction j <;> simp at *
case _ T _ _ _ => exists T; constructor; assumption; exists T; constructor
case _ ih _ =>
  intro x sp tnf
  rw[Option.bind_eq_some] at tnf; simp at tnf;
  cases tnf; case _ x' tnf =>
  cases tnf; case _ sp' tnf =>
  cases tnf; case _ tnf es =>
  cases es; case _ e1 e2 =>
  cases e1;
  have ih' := ih x sp' tnf
  cases ih'; case _ T ih =>
  exists T; cases ih; case _ ih =>
  cases ih; case _ τ' _ =>
  constructor
  · assumption;
  · sorry
sorry
sorry

-- If t is in normal form, then it is applied to enough arguments.
-- There are 2 main cases:
-- Case 1. It is an open method eg. (==)
--   So, we want all the type and instance arguments applied, meaning,
--   there is no open type mentioned in the type of the term
--   `(==) t (d :: Eq t)` is okay, `(==) t` is not okay, as the instance argument
--   is not applied
-- Case 2. It is an open function related to superclasses and fundeps
--   So, we are okay with the return type to be an open type, but it should be fully applied (no arrows allowed)
--   eg. `fdSup t (d: Ord t)` is okay, but `fdSup t` is not.


-- This property is not composable
-- In the sense that we cannot just brute force check this property for the term by
-- checking it for _all_ its subterms.
-- Obviously, `(==) t d` is fine, but `(==) t` is not and `(==) t` is a subterm of `(==) t d`
-- We need a more intelligent way of checking it


def sufficiently_applied (Γ : Ctx Term) (τ: Term) :=
  (match τ.neutral_form with
  | .some _ => true
  | .none => noOpenType Γ τ)

-- match tnf : t.neutral_form with
-- | .some (x, sp) =>
--   if Γ.is_openm x
--   then (match τ.neutral_form with
--        | .some _ => true -- to handle cases such as (supC t d) where supC : ∀t. Ord t -> Eq t, etc.
--        | .none => noOpenType Γ τ) && -- to handle applications of open functions at term level Eg. (==) t d
--        (sp.all (λ x => match x.fst with
--          | .kind => true -- this just means we have an illformed term. Typing should save us
--          | .type => noOpenType Γ x.snd
--          | .term => sufficiently_applied_neutral_form Γ sorry x.snd))
--   else true
-- | .none => true
-- decreasing_by repeat sorry


@[simp]
abbrev Confused (Γ : Ctx Term) (t : Term) : Prop := contains_variant Γ.variants [.zero, .guard, .ctor2 .choice] t

theorem partition_confusion_determined {Γ : Ctx Term}  {t : Term} : Determined Γ t <-> ¬ Confused Γ t :=
 by simp


@[simp]
abbrev DeterminedWellTyped (Γ : Ctx Term) (τ t: Term) : Prop :=
  Γ ⊢ t : τ ∧  Determined Γ t ∧ sufficiently_applied Γ τ

@[simp]
abbrev DeterminedWellTypedVal (Γ : Ctx Term) (τ t: Term) : Prop :=
  DeterminedWellTyped Γ τ t ∧ Val Γ t

-- TODO: Generalize this to mean also that open methods are fully applied


namespace Ctx

@[simp]
-- A closed context is a context where there are only pure declarations and no let, lambda bound terms
abbrev Closed (Γ : Ctx Term) : Prop :=
  ⊢ Γ ∧  ∀ (x : Nat), Γ.is_stable_red x

abbrev SpineArgWellShaped (Γ : Ctx Term) : (SpineVariant × Term) -> Prop
| (.term, t) => ∃ τ, DeterminedWellTypedVal Γ τ t
| (.type, τ) => ∃ k, Γ ⊢ τ : k
| (.kind, _) => false


@[simp]
abbrev Determined Γ := ∀ x, Γ.is_openm x ->
  ∀ sp :  List (SpineVariant × Term), ∀ σ : Term,
  σ.groundTy Γ ->
  (Γ ⊢ (#x).apply_spine sp : σ) ->
  (∀ arg ∈ sp, SpineArgWellShaped Γ arg) ->
  ∃ n, ((#x).apply_spine sp) ⟨Γ⟩⟶⋆ n ∧ DeterminedWellTyped Γ σ n

@[simp]
abbrev DeterminedClosedCtx Γ := Determined Γ ∧ Closed Γ
end Ctx


theorem closed_ctx_has_no_vars (Γ : Ctx Term) : Γ.DeterminedClosedCtx -> (∀ x, ¬ Γ.is_type x) := by
 intro h; cases h; case _ h2 =>
 simp at h2; cases h2; case _ h2 =>
 intro x; replace h2 := h2 x; intro h3; unfold Ctx.is_type at h3;
 replace h3 := type_indexing_exists h3; cases h3; case _ h3 =>
 rw[h3] at h2; unfold Frame.is_stable_red at h2; simp at h2


-- A direct proof of this lemma obviously fails
theorem NoConfusionProgressFail Γ σ t:
  Γ.Determined -> Γ.Closed -> DeterminedWellTyped Γ σ t ->
  Val Γ t ∨
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ σ t') := by
intro h1 h2 h3
have no_var := closed_ctx_has_no_vars Γ (by constructor; assumption; assumption)
simp at h3; cases h3; case _ wt noc =>
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

inductive SemDetermined (Γ : Ctx Term) : Term -> Term -> Prop
| AppTy :
  Γ.DeterminedClosedCtx ->
  τ = Term.mk_kind_apps #x τs ->
  DeterminedWellTyped Γ τ t ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ τ t') ->
  SemDetermined Γ τ t
| ArrowTy :
  Γ.DeterminedClosedCtx ->
  DeterminedWellTyped Γ (τ1 -t> τ2) f ->
  ∀ e, SemDetermined Γ τ1 e ->
  σ' = τ2 β[e] ->
  SemDetermined Γ σ' (f `@ e)
| AllTy :
  Γ.DeterminedClosedCtx ->
  DeterminedWellTyped Γ (∀[K] σ) f ->
  ∀ τ, Γ ⊢ τ : K ->
  σ' = σ β[τ] ->
  SemDetermined Γ σ' (f `@t τ)
| EqTy :
  Γ.DeterminedClosedCtx ->
  ∀ τ1 τ2, Γ ⊢ τ1 : K -> Γ ⊢ τ2 : K ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ (τ1 ~[K]~ τ2) t') ->
  SemDetermined Γ (τ1 ~[K]~ τ2) t

theorem variants_preserves_length {Γ : Ctx Term} : Γ.length = Γ.variants.length := by
induction Γ using Ctx.variants.induct <;> simp at *
· assumption

def det_ops := [CtorVariant.zero, CtorVariant.guard, CtorVariant.ctor2 Ctor2Variant.choice]

theorem frame_apply_empty [SubstitutionType T]{f : Frame T}:
  f.apply σ = Frame.empty -> f = Frame.empty := by
intro h
induction f <;> simp at *
all_goals (unfold Frame.apply at h; simp at h)

theorem temp [SubstitutionType T] {Γ Δ : Ctx T}:
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n y, σ n = .re y -> Γ.variants[n]? = Δ.variants[y]?) := by
  -- this business of d@ on lhs and [·]? on rhs is a bit of a pain.
  -- in essense the d@ returns empty when the indexing is beyond the size or the frame is actually empty
  -- in either case the indexing should land us in the same variant projection of Γ and Δ
intro h n y s
have lem := h n y s
generalize fr : Γ d@ n = f at *;
cases f
all_goals (unfold Frame.apply at lem; simp at lem; symm at lem)
· sorry
all_goals (
  have lem2 := Ctx.variant_is_sound lem (by simp)
  unfold Frame.variant at lem2; simp at lem2; rw[lem2];
  have lem1 := Ctx.variant_is_sound fr (by simp)
  unfold Frame.variant at lem1; simp at lem1; rw[lem1];
)

def mk_frame_from_variant (v : FrameVariant) : Term -> Frame Term := match v with
| .empty => λ _ => .empty
| .kind => .kind
| .type => .type
| .datatype => .datatype
| .ctor => .ctor
| .opent => .opent
| .openm => .openm
| .insttype => .insttype
| _ => λ _ => .empty


theorem variant_empty_sound[SubstitutionType T] {Γ : Ctx T} :
    Γ d@ x = .empty -> Γ.variants[x]? = .some .empty ∨ Γ.variants[x]? = .none := by
intro h
induction Γ using Ctx.variants.induct <;> simp at *
induction x <;> simp at *;
have lem := frame_apply_empty h; rw[lem]; unfold Frame.variant; simp
sorry

theorem subst_determined_stable_lemma {Γ Δ : Ctx Term} {σ : Subst Term} {e : Term}:
  (∀ n : Nat, ∀ t, σ n = .su t -> Determined Δ t) ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  Determined Γ e ->
  Determined Δ ([σ] e) := by
intro h1 h2 h3
simp at h3
generalize Γv : Γ.variants = Γvs at *;
induction Γvs, e using  contains_variant.induct generalizing Γ σ <;> simp_all
case _ n _ e =>
  generalize g : σ n = act at *;
  cases act <;> simp at *
  case re y =>
    have h2' := h2 n y g;
    generalize fr : Γ d@ n = f at *;
    cases f <;> simp at *
    case _ =>
      unfold Frame.apply at h2'; simp at h2'; symm at h2'
      have lem := variant_empty_sound h2'
      cases lem;
      all_goals (
      case _ lem => rw[lem])
    all_goals (
      unfold Frame.apply at h2'; simp at h2'; symm at h2'
      have lem := Ctx.variant_is_sound h2' (by simp)
      rw[lem])
  case su t => have h1' := h1 n t g; assumption
case _ => sorry
case _ v _ ih =>
  have lem := @variant_subst_rename_lift
  sorry
case _ =>
  have lem := temp h2
  have lem2 := variant_subst_rename_lift .term σ lem

  sorry
sorry
sorry
sorry
sorry


theorem subst_determinedwt_stable_lemma {Γ Δ : Ctx Term} {σ : Subst Term} {τ e}:
  (∀ n : Nat, ∀ t, σ n = .su t -> ∃ τ, DeterminedWellTyped Δ τ t) ->
  (∀ n y, σ n = .re y -> (Γ d@ n).apply σ = Δ d@ y) ->
  (∀ n t T, σ n = .su t -> .some T = (Γ d@ n).get_type -> Δ ⊢ t : ([σ]T)) ->
  (∀ n, Γ.is_stable n -> ∃ y, σ n = .re y) ->
  DeterminedWellTyped Γ τ e ->
  ⊢ Δ ->
  DeterminedWellTyped Δ ([σ] τ) ([σ] e) := by
intro h1 h2 h3 h4 h5 wf
simp
constructor
· cases h5; case _ h6 _ => apply subst h2 h3 h4 h6 wf
· constructor
  · cases h5; case _ h5 =>
    cases h5; case _ h5 _ =>
    simp at h5
    have lem : Determined Δ ([σ] e) :=
         @subst_determined_stable_lemma Γ Δ σ e
           (by intro n t h;
               have h1' := h1 n t h;
               cases h1'; case _ h1' =>
               cases h1'; case _ h1' =>
               cases h1'; case _ h1' =>
               assumption)
           (by assumption)
           (by simp; apply h5)
    simp at lem; assumption
  · sorry



-- Need to now show stability of determinedness over substitutions
theorem subst_determined_stable {Γ : Ctx Term} {τ τ' t e : Term} :
  DeterminedWellTyped (.type τ' :: Γ) τ t ->
  DeterminedWellTyped Γ τ' e ->
  DeterminedWellTyped Γ (τ β[e]) (t β[e]) := by
intro h1 h2
apply @subst_determinedwt_stable_lemma (Frame.type τ' :: Γ) Γ _ τ t
· intro n e h
  induction n <;> simp at *
  cases h; exists τ'
· intro n y h
  induction n <;> simp at *
  cases h; rw[Frame.apply_compose]; simp
· intro n t T h gt
  induction n <;> simp at *
  cases h; unfold Frame.get_type at gt; simp at gt; rw[gt]; simp; cases h2; assumption
· intro n h;
  induction n <;> simp at *
  unfold Frame.apply at h; simp at h; unfold Frame.is_stable at h; simp at h
· assumption
· simp at h2; cases h2; case _ h2 _ => apply judgment_ctx_wf h2


theorem NoConfusionProgressFail2 :
  SemDetermined Γ σ t ->
  Val Γ t ∨
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ σ t') := by
intro h
induction h
case _ => apply Or.inr; assumption
case _ ih =>
  cases ih
  case _ τ1 τ2 f _ _ j1 e j2 _ ih =>
    simp at j1;
    cases j1; case _ j1 _ =>
    have no_var : ∀ x, ¬ Γ.is_type x := by apply closed_ctx_has_no_vars; assumption
    have lem_prog := progress no_var j1
    cases lem_prog;
    case _ h =>
      have f_shape := canonical_lambda j1; simp at f_shape;
      replace f_shape := f_shape h j1;
      have lem := classification_lemma j1; simp at j1; cases lem;
      case _ h => cases h
      case _ h =>
        cases h;
        case _ h => have lem := classification_lemma h; cases h
        case _ h => cases h; case _ h => cases h; case _ h =>
          have lem := invert_arr_kind h; cases lem;
          replace f_shape := f_shape h
          have lem : ArrowLike (τ1 -t> τ2) := by constructor
          replace f_shape := f_shape lem;
          induction f_shape
          case _ τ t _ =>
            apply Or.inr
            have lem : τ = τ1 := lam_typing_unique2 j1; cases lem
            exists (t β[e])  --> needs substitution is stable over NoConfusion
            constructor
            sorry
            sorry

          case _ => /- illtyped (Λ[k] f `@ t) -/ cases j1
          case _ vh _ => /- (ctor `@ e) is a value -/
            apply Or.inl;
            cases vh; case _ t _ _ nf =>
              cases nf; case _ w nf ctor =>
              constructor
              have lem := Term.neutral_form_law nf
              rw[<-lem]; simp; rw[Option.bind_eq_some];
              exists w; simp;
              constructor;
              rw[lem]; apply Eq.symm nf
              constructor; exact rfl; exact rfl
              simp at ctor;  apply Frame.is_ctor_implies_is_stable_red ctor
          case _ vh _ => /- inst `@ e -/
            apply Or.inl;
            cases vh; case _ t _ _ nf =>
              cases nf; case _ w nf inst =>
              constructor
              have lem := Term.neutral_form_law nf
              rw[<-lem]; simp; rw[Option.bind_eq_some];
              exists w; simp;
              constructor;
              rw[lem]; apply Eq.symm nf
              constructor; exact rfl; exact rfl
              simp at inst;  apply Frame.is_insttype_implies_is_stable_red inst

          case _ => simp at * --> contradiction
    case _ h =>
      cases h
      case _ h =>

        sorry
      case _ h => exfalso; cases h; simp at *
  case _ ih =>
    cases ih; case _ f _ _ _ _ _ _ e' ih =>
    cases ih;
    apply Or.inr; exists (f `@ e');
    constructor;
    case _ h1 _ _ _ _ h2 =>
      simp at h1; cases h1;
      simp at h2; cases h2;
      case _ j1 _ j2 _ =>
      sorry
    -- sorry
    simp; constructor
    · sorry -- -t> bullshit
    · constructor;
      case _ h _ _ _ _ _ => simp at h; cases h; sorry -- assumption
      case _ h => simp at h; cases h; sorry -- assumption

case _ => sorry
case _ => apply Or.inr; assumption


-- Determined needs to be defined using a recursive function.
-- But we cannot because substitutions get in the way
def SemDetermined' (Γ : Ctx Term) : Term -> (Term -> Prop)
| τ1 -t> τ2 => λ f =>
  Γ.DeterminedClosedCtx ->
  DeterminedWellTyped Γ (τ1 -t> τ2) f ->
  ∀ e, SemDetermined' Γ τ1 e ->
  -- σ' = τ2 β[e] ->
  SemDetermined' Γ (τ2 β[e]) (f `@ e)
| ∀[K] σ => λ f =>
  Γ.DeterminedClosedCtx ->
  DeterminedWellTyped Γ (∀[K] σ) f ->
  ∀ τ, Γ ⊢ τ : K ->
  -- σ' = σ β[τ] ->
  SemDetermined' Γ (σ β[τ]) (f `@t τ)
| (τ1 ~[K]~ τ2) => λ t => -- in this case t should just step to refl
  Γ.DeterminedClosedCtx ->
  Γ ⊢ τ1 : K -> Γ ⊢ τ2 : K ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ (τ1 ~[K]~ τ2) t') ->
  SemDetermined' Γ (τ1 ~[K]~ τ2) t
| τ => λ t =>
  Γ.DeterminedClosedCtx ->
  ∃ x τs, τ = Term.mk_kind_apps #x τs ->
  DeterminedWellTyped Γ τ t ->
  (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ τ t') ->
  SemDetermined' Γ τ t
-- termination_by λ τ t =>  sorry
decreasing_by
  case _ => unfold sizeOf; unfold sizeOf_Term; simp; omega
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry


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

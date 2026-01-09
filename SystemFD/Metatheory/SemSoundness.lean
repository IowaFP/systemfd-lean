-- import SystemFD.Term
-- import SystemFD.Term.Subexpression
-- import SystemFD.Term.Variant
-- import SystemFD.Metatheory.Canonicity
-- import SystemFD.Metatheory.Confluence
-- import SystemFD.Metatheory.Progress
-- import SystemFD.Metatheory.Preservation

-- set_option maxHeartbeats 500000

-- /-

-- Goal
-- ----

-- We want to have a syntactic property P on terms of SystemFD
-- (possibly indexed over types and context)
-- st. the following holds for it:

--    P τ t ⇒
--    ∃ n, (t ⟶⋆ n) ∧
--         (Val Γ n ∧ n is confusion free)
--         ∨ ( does not have a normal form)

-- The context Γ has to bear some responsibility for the term to be confusion free,
-- as the · ⟶⋆ · relation is dependent on Γ for instantiating open methods. We call this
-- property saturation. Intuitively, the saturation property enforces that the
-- (well typed) open method call instantiations cannot cause confusion.

-- To explicitly encode this property in our formalization:

--    SatCtx Γ ∧ P τ Γ t ⇒
--    ∃ n, (t ⟨Γ⟩⟶⋆ n) ∧
--         (Val Γ n ∧ n is confusion free)
--          ∨ n does not have a normal form


-- Confusion Free (or (Weakly) Determined):
-- ---------------

-- Idea 1:

-- Determined Γ τ t

-- A (well typed) term, t,
-- 1. t does not contain `0 or ⊕ or guards (at the head)
-- 2. open methods are fine but they need to be fully applied -- enforced by typing?


-- Idea 2:
-- DeterminedTyping Γ t τ

-- Deeply checked  Idea 1. check that t does not contain `0, ⊕ etc only at the head but for all subterms of t

-- theorem : NoConfusion Γ → Closed Γ → DetermindedTyping Γ t τ
--           Val Γ t  ∨ (∃ t', t ⟶+ t' ∧ DetermindedTyping Γ t' τ)

-- m [τs] ds : σ

-- NoConfusion Γ

--     ∀ τs ds,
--       (τs are ground, ds are DeterminedTyping Γ σ d, σ is ground)
--     ∃ i, Γ d@ i = .inst #m t ∧ t [τs] ds - ̸⟶⋆ `0 ∧
--     ∀ k, k ≠ i ∧  Γ d@ k = .inst #m t' ∧ t' [τs] ds ⟶⋆ `0

-- Captures: Saturation.
-- 1. Instance existence --> no `0
-- 2. Instance uniqueness --> no ⊕


-- Equivalent to:
-- ∀ m [τs] ds : σ ⟶+ n, DeterminedTyping Γ n σ


-- -/

-- namespace Term

-- def mk_ty_tm_app (t : Term) (τs : List Term) (es : List Term) := (t.mk_ty_apps τs).mk_apps es
-- notation:70 t:170 "⬝[" τs:170 "]⬝" es:170 "⬝" => mk_ty_tm_app t τs es

-- -- Ground Types are the ones that are not lambda bound
-- -- Int, Bool, Int → Bool, Maybe, Maybe Int are all ground types
-- -- a → Int, Maybe a are not ground types
-- def groundTy (Γ : Ctx Term) : Term -> Bool
-- | #x => Γ.is_datatype x || Γ.is_opent x
-- | (τ1 -t> τ2) => groundTy Γ τ1 && groundTy (.empty :: Γ) τ2
-- | τ1 `@k τ2 => groundTy Γ τ1 && groundTy  Γ τ2
-- | _ => false

-- end Term

-- namespace Ctx

-- end Ctx

-- @[simp]
-- def noOpenType (Γ : Ctx Term) : Term -> Bool
-- | #x => ¬ Γ.is_openm x
-- | (τ -t> τ') => noOpenType Γ τ ∧ noOpenType (.type τ :: Γ) τ'
-- | ∀[K] τ => noOpenType (.kind K :: Γ) τ
-- | τ `@k τ' => noOpenType Γ τ ∧ noOpenType Γ τ'
-- | _ => false

-- @[simp]
-- abbrev Determined (Γ : Ctx Term) (t : Term) : Prop :=
--   (¬ contains_variant Γ.variants [.zero, .guard, .ctor2 .choice] t)

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




-- Spine type collects prefixes
-- Need to have some connection between the type elements of the spine and the original type
-- Try to repurpose SpineType here

inductive DetSpineType : Ctx Term -> List (SpineVariant × Term) -> Term -> Term -> Prop where
| refl :
  DetSpineType Γ [] T T
| arrow :
  Γ ⊢ a : A ->
  sufficiently_applied Γ A ->
  Γ ⊢ (A -t> B) : ★ ->
  DetSpineType Γ sp (B β[a]) T ->
  DetSpineType Γ ((.term, a) :: sp) (A -t> B) T
| all :
  Γ ⊢ a : A ->
  sufficiently_applied Γ a -> -- is this correct?
  Γ ⊢ (∀[A] B) : ★ ->
  DetSpineType Γ sp (B β[a]) T ->
  DetSpineType Γ ((.type, a) :: sp) (∀[A] B) T
| arrowk :
  Γ ⊢ a : A ->
  Γ ⊢ (A -k> B) : □ ->
  DetSpineType Γ sp B T ->
  DetSpineType Γ ((.kind, a) :: sp) (A -k> B) T

@[simp]
abbrev NeutralFormSpineType : (v : JudgmentVariant) -> (Γ : Ctx Term) -> (JudgmentArgs v) -> Prop
| .prf => λ Γ => λ(t , τ) => sufficiently_applied Γ τ ->
              ∀ x, ∀sp, t.neutral_form = .some (x, sp) ->
              (∃ T, .some T = (Γ d@ x).get_type ∧ ∃ τ' , DetSpineType Γ sp τ' T)
| .wf => λ _ => λ _ => true


theorem neutral_form_spine_type :
  Judgment v Γ ix ->
  NeutralFormSpineType v Γ ix
   := by
intro j; induction j <;> simp at *
case _ T _ _ _ =>
  intros; exists T; constructor; assumption; exists T; constructor
case _ ih _ => -- appk bogus case
  intro h x sp tnf
  rw[Option.bind_eq_some] at tnf; simp at tnf;
  cases tnf; case _ x' tnf =>
  cases tnf; case _ sp' tnf =>
  cases tnf; case _ tnf es =>
  cases es; case _ e1 e2 =>
  cases e1;
  sorry
  -- have ih' := ih _ x sp' tnf
  -- cases ih'; case _ T ih =>
  -- exists T; cases ih; case _ ih =>
  -- cases ih; case _ τ' _ =>
  -- constructor
  -- · assumption;
  -- · sorry
case _ => -- arrow
  intro h x sp tnf
  rw[Option.bind_eq_some] at tnf; simp at tnf;
  cases tnf; case _ x' tnf =>
  cases tnf; case _ sp' tnf =>
  cases tnf; case _ tnf es =>
  cases es; case _ e1 e2 =>
  cases e1;
  sorry

case _ => -- appt
  sorry

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

abbrev DeterminedClosedCtx Γ := Determined Γ ∧ Closed Γ
end Ctx


theorem closed_ctx_has_no_vars (Γ : Ctx Term) : Γ.DeterminedClosedCtx -> (∀ x, ¬ Γ.is_type x) := by
 intro h; cases h; case _ h2 =>
 simp at h2; cases h2; case _ h2 =>
 intro x; replace h2 := h2 x; intro h3; unfold Ctx.is_type at h3;
 replace h3 := type_indexing_exists h3; cases h3; case _ h3 =>
 rw[h3] at h2; unfold Frame.is_stable_red at h2; simp at h2

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
· cases h2; case _ h2 _ => apply judgment_ctx_wf h2

@[simp]
abbrev  NoConfusionProgressType (Γ : Ctx Term) : (v : JudgmentVariant) -> (JudgmentArgs v) -> Prop
| .prf => λ (t, σ) =>
  DeterminedWellTyped Γ σ t ->
  Val Γ t ∨ (∃ t', t ⟨Γ⟩⟶+ t' ∧ DeterminedWellTyped Γ σ t')
| .wf => λ _ => true

-- A direct proof of this lemma obviously fails
theorem NoConfusionProgress Γ v idx :
  Γ.DeterminedClosedCtx ->
  Judgment v Γ idx ->
  NoConfusionProgressType Γ v idx := by
intro h1 h3
cases h1; case _ h1 h2 =>
have no_var := closed_ctx_has_no_vars Γ (by constructor; assumption; assumption)
induction h3 <;> simp
all_goals (intro j)
case _ Γ A t b T _ j' j'' _ _ _ _ _ =>
  intro h3 h4 h5 h6;
  apply Or.inr
  generalize th : b β[t] = t' at *;
  exists t';
  constructor
  · rw[<-th]; apply RedPlus.step (RedStar.refl) Red.letbeta
  · have d1 : DeterminedWellTyped Γ T (A.letterm t b) := by
         constructor
         · assumption
         · constructor
           simp; constructor; constructor; assumption; assumption; assumption; assumption
    have d2 : DeterminedWellTyped Γ A t := by
      constructor
      · assumption
      · constructor; simp; assumption; sorry
    have d3 : DeterminedWellTyped Γ T t' := sorry
    constructor
    · have lem := beta_term j'' j'
      rw[th] at lem;
      rw[Subst.apply_compose_commute] at lem; simp at lem; assumption
    · constructor
      · sorry
      · assumption
case _ => intro d1; apply Or.inl; apply Val.star
case _ => sorry
case _ => intros; apply Or.inl; apply Val.arrk
case _ => intros; apply Or.inl; apply Val.all
case _ => intros; apply Or.inl; apply Val.arr
case _ => intros; apply Or.inl; sorry
case _ => intros; apply Or.inl; apply Val.eq
case _ => sorry
case _ => intros; apply Or.inl; apply Val.lam
case _ => sorry
case _ => intros; apply Or.inl; apply Val.lamt
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry
case _ => sorry




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

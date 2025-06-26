import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Term.Variant
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Progress
import SystemFD.Metatheory.Preservation
import SystemFD.Metatheory.Inversion

-- Haskell Style Statically Determined Instances (HSSDI)

-- Idea:
-- Every open method definition should look like this:
-- λ ... λ guard ... guard body
-- i.e., a preamble of lambdas followed by a preamble of guards followed by a body
-- Moreover, every guard should be relative to some constant open instance pattern

-- Every invocation of an open method should be applied to concrete instances
-- where the specified instances exist in the preamble of guards

-- For example: `eq Bool BoolEq a b` with:
-- `eq = λ t i a b. guard BoolEq i with body`
-- is HSSDI
-- Moreover, it reduces to: `body a b`

-- Claim: If a SystemFD term is HSSDI then it cannot reduce to 0

def unfold_openm (Γ : Ctx Term) : Nat -> Nat -> Term -> Term
| n + 1, x, #v =>
  if x == v then
    match (Γ d@ x) with
    | .openm _ =>
      let ιs := get_instances Γ x
      let ιs' := List.map (unfold_openm Γ n x ·) ιs
      List.foldl (·⊕·) `0 ιs'
    | _ => #v
  else #v
| n + 1, x, .ctor1 v t =>
  let t' := unfold_openm Γ (n + 1) x t
  .ctor1 v t'
| n + 1, x, .ctor2 v t1 t2 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  .ctor2 v t1' t2'
| n + 1, x, .bind2 v t1 t2 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  .bind2 v t1' t2'
| n + 1, x, .letterm t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .letterm t1' t2' t3'
| n + 1, x, .guard t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .guard t1' t2' t3'
| n + 1, x, .ite t1 t2 t3 t4 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  let t4' := unfold_openm Γ (n + 1) x t4
  .ite t1' t2' t3' t4'
| n + 1, x, .eq t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .eq t1' t2' t3'
| _ + 1, _, `0 => `0
| _ + 1, _, ★ => ★
| _ + 1, _, □ => □
| 0, _, t => t
termination_by n _ t => (n, t.size)

def elim_openm (Γ : Ctx Term) (n : Nat) : Term -> Term
| #x =>
  match (Γ d@ x) with
  | .openm _ => unfold_openm Γ n x #x
  | _ => #x
| .ctor1 v t =>
  let t' := elim_openm Γ n t
  .ctor1 v t'
| .ctor2 v t1 t2 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  .ctor2 v t1' t2'
| .bind2 v t1 t2 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  .bind2 v t1' t2'
| .letterm t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .letterm t1' t2' t3'
| .guard t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .guard t1' t2' t3'
| .ite t1 t2 t3 t4 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  let t4' := elim_openm Γ n t4
  .ite t1' t2' t3' t4'
| .eq t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .eq t1' t2' t3'
| `0 => `0
| ★ => ★
| □ => □

@[simp]
abbrev HssdiCondition (Γ : Ctx Term) (t : Term) : Prop :=
  ¬ ContainsVariant Γ.variants [.guard, .zero, .var .openm, .var .term] t

theorem hssdi_no_zero_preservation_step :
  Γ ⊢ t : A ->
  HssdiCondition Γ t ->
  Red Γ t t' ->
  HssdiCondition Γ t'
:= by
intro j h r; simp at h
induction r generalizing A
case beta =>
  replace h := not_contains_variant_ctor2 h
  have h' := not_contains_variant_bind2 h.1
  replace h := h.2
  simp; intro h
  replace h := contains_variant_from_beta (bind2_frame_variant .lam) h
  cases h
  case _ q => apply h'.2 q
  case _ q => apply h q
case betat =>
  replace h := not_contains_variant_ctor2 h
  have h' := not_contains_variant_bind2 h.1
  replace h := h.2
  simp; intro h
  replace h := contains_variant_from_beta (bind2_frame_variant .lamt) h
  cases h
  case _ q => apply h'.2 q
  case _ q => apply h q
case letbeta =>
  replace h := not_contains_variant_letterm h
  intro h
  replace h := contains_variant_from_beta .term h
  cases h
  case _ q => apply h.2.2 q
  case _ q => apply h.2.1 q
case cast =>
  replace h := not_contains_variant_ctor2 h
  apply h.1
case sym =>
  replace h := not_contains_variant_ctor1 h
  apply h
case seq =>
  replace h := not_contains_variant_ctor2 h
  apply h.1
case appc =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h1 := not_contains_variant_ctor2 h1
  cases h1; case _ h1 h3 =>
  replace h1 := not_contains_variant_ctor2 h1
  replace h2 := not_contains_variant_ctor2 h2
  intro q; cases q; simp at *
  case _ q => apply h1.2 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h3 q
    case _ q => apply h2.2 q
case apptc =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h1 := not_contains_variant_ctor2 h1
  cases h1; case _ h1 h3 =>
  replace h3 := not_contains_variant_bind2 h3
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro q; cases q; simp at *
  case _ q => apply h1 q
  case _ q =>
    replace q := contains_variant_from_beta .kind q
    cases q
    case _ q => apply h3.2 q
    case _ q => apply h2.2 q
case fst =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h2 := not_contains_variant_ctor2 h2
  cases h2; case _ h2 h3 =>
  replace h3 := not_contains_variant_ctor2 h3
  simp; intro q; cases q; simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2 q
  case _ q => apply h3.1 q
case snd =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h2 := not_contains_variant_ctor2 h2
  cases h2; case _ h2 h3 =>
  replace h3 := not_contains_variant_ctor2 h3
  simp; intro q; cases q; simp at *
  case _ q => apply h1 q
  case _ q => apply h3.2 q
case allc Γ _ _ _ =>
  replace h := not_contains_variant_bind2 h
  cases h; case _ h1 h2 =>
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro q; cases q; simp at *
  case _ q =>
    cases j; case _ j1 j2 =>
    cases j2; case _ j2 j3 =>
    apply h2.1
    have lem := @contains_variant_rename
      Γ.variants
      (bind2_frame_variant .allc :: Γ.variants)
      [.guard, .zero, .var .openm, .var .term]
      ★
      (λ x => x + 1)
    simp at lem; apply lem.1 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.2 q
case arrowc =>
  replace h := not_contains_variant_bind2 h
  cases h; case _ h1 h2 =>
  replace h1 := not_contains_variant_ctor2 h1
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro q; cases q; simp at *
  case _ q => apply h1.1 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1.2 q
    case _ q => apply h2.2 q
case choice1 =>
  exfalso; apply h
  apply ContainsVariant.ctor2_1
  constructor; simp
case choice2 =>
  exfalso; apply h
  apply ContainsVariant.ctor2_2
  constructor; simp
case ite_matched p x sp s sp' q Γ b e q1 q2 q3 q4 =>
  replace h := not_contains_variant_ite h
  intro q; replace q := contains_variant_spine.1 q
  cases q
  case _ w => apply h.2.2.1 w
  case _ w =>
    cases w; case _ t w =>
    cases w; case _ w1 w2 =>
    have lem : t ∈ sp' := by
      have lem := prefix_equal_law q3
      subst lem; simp; apply Or.inr w1
    have h1 := Term.neutral_form_law q2
    rw [<-h1] at h; apply h.2.1
    apply contains_variant_spine.2; apply Or.inr
    apply Exists.intro t; apply And.intro lem w2
case ite_missed =>
  replace h := not_contains_variant_ite h; simp
  intro q; apply h.2.2.2 q
case guard_matched => exfalso; apply h; constructor; simp
case guard_missed => exfalso; apply h; constructor; simp
case inst q1 q2 q3 q4 q5 =>
  replace q1 := Term.neutral_form_law q1
  rw [<-q1] at h; exfalso
  apply h; apply contains_variant_spine.2
  apply Or.inl; constructor; simp
  apply Or.inl; rfl
  apply Ctx.variant_is_openm q2
case letterm q1 q2 =>
  replace q1 := Term.neutral_form_law q1
  rw [<-q1] at h; exfalso
  apply h; apply contains_variant_spine.2
  apply Or.inl; constructor; simp
  apply Or.inr; rfl
  apply Ctx.variant_is_sound (Eq.symm q2); simp
case ctor1_congr ih =>
  replace j := invert_ctor1 j
  cases j; case _ B j =>
  replace h := not_contains_variant_ctor1 h
  replace ih := ih j h; simp at ih
  intro h; cases h
  case _ q => simp at q
  case _ q => apply ih q
case ctor2_congr1 ih =>
  replace j := invert_ctor2 j
  cases j; case _ B j =>
  cases j; case _ C j =>
  replace h := not_contains_variant_ctor2 h
  replace ih := ih j.1 h.1; simp at ih
  intro h; cases h
  case _ q => simp at q
  case _ q => apply ih q
  case _ q => apply h.2 q
case ctor2_congr2 ih =>
  replace j := invert_ctor2 j
  cases j; case _ B j =>
  cases j; case _ C j =>
  replace h := not_contains_variant_ctor2 h
  replace ih := ih j.2 h.2; simp at ih
  intro h; cases h
  case _ q => simp at q
  case _ q => apply h.1 q
  case _ q => apply ih q
case bind2_congr1 ih =>
  replace j := invert_bind2 j
  cases j; case _ B j =>
  cases j; case _ C j =>
  replace h := not_contains_variant_bind2 h
  replace ih := ih j.1 h.1; simp at ih
  intro h; cases h
  case _ q => simp at q
  case _ q => apply ih q
  case _ q => apply h.2 q
case bind2_congr2 v _ _ _ _ _ _ ih =>
  replace j := invert_bind2 j
  cases j; case _ B j =>
  cases j; case _ C j =>
  replace h := not_contains_variant_bind2 h
  cases v <;> simp at *
  all_goals (
    replace ih := ih j.2 h.2; simp at ih
    intro h; cases h
    case _ q => simp at q
    case _ q => apply h.1 q
    case _ q => apply ih q
  )
case ite_congr  ih =>
  cases j; case _ j1 j2 j3 j4 j5 j6 j7 j8 j9 =>
  replace h := not_contains_variant_ite h
  replace ih := ih j5 h.2.1; simp at ih
  intro h; cases h
  case _ q => simp at q
  case _ q => apply h.1 q
  case _ q => apply ih q
  case _ q => apply h.2.2.1 q
  case _ q => apply h.2.2.2 q
case guard_congr => exfalso; apply h; constructor; simp
case ctor1_absorb =>
  exfalso; apply h
  apply ContainsVariant.ctor1_
  constructor; simp
case ctor2_absorb1 =>
  exfalso; apply h
  apply ContainsVariant.ctor2_1
  constructor; simp
case ctor2_absorb2 =>
  exfalso; apply h
  apply ContainsVariant.ctor2_2
  constructor; simp
case bind2_absorb1 =>
  exfalso; apply h
  apply ContainsVariant.bind2_1
  constructor; simp
case bind2_absorb2 =>
  exfalso; apply h
  apply ContainsVariant.bind2_2
  constructor; simp
case ite_absorb =>
  exfalso; apply h
  apply ContainsVariant.ite2
  constructor; simp
case guard_absorb =>
  exfalso; apply h
  apply ContainsVariant.guard2
  constructor; simp
case ctor1_map =>
  replace h := not_contains_variant_ctor1 h
  replace h := not_contains_variant_ctor2 h
  simp; intro h2
  cases h2 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h.1 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h.2 q
case ctor2_map1 =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h1 := not_contains_variant_ctor2 h1
  simp; intro h2
  cases h2 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1.1 q
    case _ q => apply h2 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1.2 q
    case _ q => apply h2 q
case ctor2_map2 =>
  replace h := not_contains_variant_ctor2 h
  cases h; case _ h1 h2 =>
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro h3
  cases h3 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.1 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.2 q
case bind2_map1 =>
  replace h := not_contains_variant_bind2 h
  cases h; case _ h1 h2 =>
  replace h1 := not_contains_variant_ctor2 h1
  simp; intro h2
  cases h2 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1.1 q
    case _ q => apply h2 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1.2 q
    case _ q => apply h2 q
case bind2_map2 =>
  replace h := not_contains_variant_bind2 h
  cases h; case _ h1 h2 =>
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro h3
  cases h3 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.1 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.2 q
case ite_map =>
  replace h := not_contains_variant_ite h
  cases h; case _ h1 h2 =>
  cases h2; case _ h2 h3 =>
  cases h3; case _ h3 h4 =>
  replace h2 := not_contains_variant_ctor2 h2
  simp; intro h3
  cases h3 <;> simp at *
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.1 q
    case _ q => apply h3 q
    case _ q => apply h4 q
  case _ q =>
    cases q; simp at *
    case _ q => apply h1 q
    case _ q => apply h2.2 q
    case _ q => apply h3 q
    case _ q => apply h4 q
case guard_map => exfalso; apply h; constructor; simp

theorem hssdi_no_zero_preservation :
  Γ ⊢ t : A ->
  HssdiCondition Γ t ->
  RedStar Γ t t' ->
  HssdiCondition Γ t'
:= by
intro j h r
induction r; apply h
case _ r1 r2 ih =>
  replace j := preservation j r1
  apply hssdi_no_zero_preservation_step j ih r2

theorem hssdi_no_zero_step :
  HssdiCondition Γ t ->
  ¬ Red Γ t `0
:= by
have lem1 : ∀ b t, `0 = b β[t] -> `0 = b ∨ (b = #0 ∧ t = `0) := by
  intro b t
  induction b <;> simp at *
  case _ x =>
    cases x <;> simp at *
    intro h; subst h; rfl
have lem2 : ∀ t sp, `0 = t.apply_spine sp -> t = `0 ∧ sp = [] := by
  intro t sp h
  induction sp generalizing t <;> simp at *
  case _ => rw [h]
  case _ hd tl ih =>
    cases hd; case _ sv a =>
    cases sv
    all_goals (
      simp at h
      replace ih := ih _ h
      cases ih; case _ e1 e2 =>
      injection e1
    )
intro h r; simp at h
generalize sdef : `0 = s at r
induction r
all_goals (try simp at *)
case beta =>
  replace sdef := lem1 _ _ sdef
  cases sdef
  case _ h =>
    subst h; apply h
    apply ContainsVariant.ctor2_1
    apply ContainsVariant.bind2_2
    constructor; simp
  case _ h =>
    cases h; case _ e1 e2 =>
    subst e1; subst e2; apply h
    apply ContainsVariant.ctor2_2
    constructor; simp
case betat =>
  replace sdef := lem1 _ _ sdef
  cases sdef
  case _ h =>
    subst h; apply h
    apply ContainsVariant.ctor2_1
    apply ContainsVariant.bind2_2
    constructor; simp
  case _ h =>
    cases h; case _ e1 e2 =>
    subst e1; subst e2; apply h
    apply ContainsVariant.ctor2_2
    constructor; simp
case letbeta =>
  replace sdef := lem1 _ _ sdef
  cases sdef
  case _ h =>
    subst h; apply h
    apply ContainsVariant.letterm3
    constructor; simp
  case _ h =>
    cases h; case _ e1 e2 =>
    subst e1; subst e2; apply h
    apply ContainsVariant.letterm2
    constructor; simp
case cast =>
  subst sdef; apply h
  apply ContainsVariant.ctor2_1
  constructor; simp
case choice1 =>
  apply h; apply ContainsVariant.ctor2_1
  constructor; simp
case choice2 =>
  apply h; apply ContainsVariant.ctor2_2
  constructor; simp
case ite_matched =>
  have lem := lem2 _ _ sdef
  cases lem; case _ e1 e2 =>
  subst e1; subst e2
  apply h; apply ContainsVariant.ite3
  constructor; simp
case ite_missed =>
  subst sdef; apply h
  apply ContainsVariant.ite4
  constructor; simp
case guard_matched => exfalso; apply h; constructor; simp
case guard_missed => exfalso; apply h; constructor; simp
case letterm y h x sp Γ t q1 q2 =>
  have lem := lem2 _ _ sdef
  cases lem; case _ e1 e2 =>
  subst e1; subst e2
  have q3 := Term.neutral_form_law q1; simp at q3
  subst q3; apply h
  apply ContainsVariant.var; simp
  apply Or.inr; rfl
  have lem := Ctx.variant_is_sound (by rw [<-q2])
  unfold Frame.variant at lem; simp at lem
  apply lem
case inst h x sp tl Γ tl' h' q1 q2 q3 q4 q5 =>
  have lem2 := Term.neutral_form_law q1
  rw [<-lem2] at h
  replace h2 := not_contains_variant_spine h
  apply h2.1; constructor
  simp; apply Or.inl; rfl
  have lem := Ctx.variant_is_openm q2
  apply lem
case ctor1_absorb =>
  apply h; apply ContainsVariant.ctor1_
  constructor; simp
case ctor2_absorb1 =>
  apply h; apply ContainsVariant.ctor2_1
  constructor; simp
case ctor2_absorb2 =>
  apply h; apply ContainsVariant.ctor2_2
  constructor; simp
case bind2_absorb1 =>
  apply h; apply ContainsVariant.bind2_1
  constructor; simp
case bind2_absorb2 =>
  apply h; apply ContainsVariant.bind2_2
  constructor; simp
case guard_absorb => exfalso; apply h; constructor; simp
case ite_absorb =>
  apply h; apply ContainsVariant.ite2
  constructor; simp

theorem syntactic_guarantee_of_reduction_to_zero_impossible :
  Γ ⊢ t : A ->
  HssdiCondition Γ t ->
  ¬ RedStar Γ t `0
:= by
intro j h r
generalize sdef : `0 = s at r
induction r
case refl =>
  subst sdef; simp at h
  apply h; constructor; simp
case step y z r1 r2 ih =>
  subst sdef
  have lem := hssdi_no_zero_preservation j h r1
  apply hssdi_no_zero_step lem r2

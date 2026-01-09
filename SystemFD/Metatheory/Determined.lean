import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Term.Variant
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Inversion
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Substitution
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Progress

def Term.Determined (Γ : List FrameVariant) (t : Term) : Prop :=
  ¬ ContainsVariant Γ [.ctor2 .choice, .guard, .zero] t

@[simp]
def Determined.ctor1 : Term.Determined Γ (.ctor1 v t) <-> Term.Determined Γ t := by
  apply Iff.intro
  intro h; apply not_contains_variant_ctor1 h
  intro h1 h2; cases h2
  case _ h3 => cases v <;> simp at h3
  case _ h3 => apply h1 h3

@[simp]
def Determined.ctor2 :
  Term.Determined Γ (.ctor2 v t1 t2)
  <-> v ≠ .choice ∧ Term.Determined Γ t1 ∧ Term.Determined Γ t2
:= by
  apply Iff.intro
  intro h; apply And.intro _; apply not_contains_variant_ctor2 h
  cases v <;> simp at *; apply h; constructor; simp
  intro h1 h2; cases h2
  case _ h3 => cases v <;> simp at h3; apply h1.1 rfl
  case _ h3 => apply h1.2.1 h3
  case _ h3 => apply h1.2.2 h3

@[simp]
def Determined.bind2 :
  Term.Determined Γ (.bind2 v t1 t2)
  <-> Term.Determined Γ t1 ∧ Term.Determined (bind2_frame_variant v::Γ) t2
:= by
  apply Iff.intro
  intro h; apply not_contains_variant_bind2 h
  intro h; rcases h with ⟨h1, h2⟩; intro h3
  cases h3
  case _ h3 => cases v <;> simp at h3
  case _ h3 => apply h1 h3
  case _ h3 => apply h2 h3

def Determined.beta (f : FrameVariant) :
  Term.Determined (f::Γ) b ->
  Term.Determined Γ a ->
  Term.Determined Γ (b β[a])
:= by
  intro h1 h2 h3
  replace h3 := contains_variant_from_beta f h3
  cases h3
  case _ h3 => apply h1 h3
  case _ h3 => apply h2 h3

def Determined.openm (Γ : Ctx Term) (i : Nat) : Prop :=
  ∀ T G sp,
    Γ d@ i = .openm T ->
    sp.length ≥ T.arity ->
    SpineType Γ sp T G ->
    ∃ t, RedPlus Γ (Term.apply_spine #i sp) t ∧ Term.Determined Γ.variants t

def Determined.letterm (Γ : Ctx Term) (i : Nat) : Prop :=
  ∀ T t, Γ d@ i = .term T t -> Term.Determined Γ.variants t

def Ctx.Determined (Γ : Ctx Term) : Prop :=
  ∀ i, Determined.openm Γ i ∧ Determined.letterm Γ i

@[simp]
abbrev DeterminedProgressLemmaType (Γ : Ctx Term) : (v : JudgmentVariant) -> JudgmentArgs v -> Prop
| .prf => λ (t, _) =>
  t.Determined Γ.variants ->
  Γ.Determined ->
  Val Γ t ∨ (∃ t', RedPlus Γ t t' ∧ t'.Determined Γ.variants)
| .wf => λ () => True

theorem determined_progress_lemma :
  (∀ x, ¬ Γ.is_type x) ->
  Judgment v Γ ix ->
  DeterminedProgressLemmaType Γ v ix
:= by
  intro h j; induction j <;> simp <;> intros
  case ax => apply Or.inl; apply Val.star
  case letterm Γ A t b T j1 j2 j3 j4 ih1 ih2 ih3 ih4 =>
    sorry
    -- apply Or.inr; apply Exists.intro (b β[t])
    -- apply And.intro; apply RedPlus.one Red.letbeta
    -- cases dt; case _ d1 d2 d3 =>
    -- sorry
  case var Γ x T j1 j2 ih dx dΓ =>
    have j3 := Judgment.var j1 j2
    replace h := h x
    generalize fdef : Γ d@ x = f at *
    cases f <;> simp [Frame.get_type] at *
    all_goals rw [fdef] at h; simp [Frame.is_type] at h
    all_goals subst j2; clear ih h
    case openm =>
      cases Nat.decLt 0 T.arity
      case _ h =>
        generalize zdef : T.to_telescope = z
        rcases z with ⟨γ, G⟩; simp at h
        have lem0 := inversion_apply_spine (sp := []) j3
        rcases lem0 with ⟨C, q1, q2, q3⟩
        cases q2; case _ c q2 =>
        clear c; rw [fdef] at q2; simp [Frame.get_type] at q2; subst q2
        replace dΓ := (dΓ x).1 C C [] fdef (by simp; exact h) q1
        rcases dΓ with ⟨t, r, dt⟩
        apply Or.inr; apply Exists.intro t
        apply And.intro r dt
      case _ h =>
        apply Or.inl; apply Val.app (x := x) (sp := []); simp
        apply Or.inr; simp [OpenVarVal]; rw [fdef]; simp [Frame.is_openm]
        intro S sh; simp [Frame.get_type] at sh; subst sh
        apply h
    case term t =>
      have lem := (dΓ x).2 T t fdef
      apply Or.inr; apply Exists.intro t
      apply And.intro _ lem
      apply RedPlus.one
      have r := @Red.letterm #x x [] Γ T t; simp at r
      apply r; rw [fdef]
    all_goals
      apply Or.inl; apply Val.app x []; simp
      apply Or.inl; simp; rw [fdef]; simp [Frame.is_stable_red]
  case allk => apply Or.inl; apply Val.arrk
  case allt => apply Or.inl; apply Val.all
  case arrow => apply Or.inl; apply Val.arr
  case appk Γ f A B a j1 j2 ih1 ih2 df da dΓ =>
    have lem1 := classification_lemma j1; simp at lem1
    rcases lem1 with ⟨lem1⟩ | ⟨K, j3, j4⟩; rotate_left
    cases j4; cases j3; cases lem1; case _ j3 j4 =>
    have j5 := Judgment.appk j1 j2
    apply Or.inl; apply types_are_values j5 j4
  case eq => apply Or.inl; apply Val.eq
  case ite => sorry
  case guard dt _ => exfalso; apply dt; constructor; simp
  case lam => apply Or.inl; apply Val.lam
  case app Γ f A B a B' j1 j2 j3 ih1 ih2 df da dΓ =>
    simp at ih1 h; replace ih1 := ih1 h df dΓ
    rcases ih1 with ⟨ih1⟩ | ⟨f', r, ih1⟩; rotate_left
    apply Or.inr; apply Exists.intro (f' `@ a)
    apply And.intro; apply RedPlus.ctor2_congr1 rfl r
    apply Determined.ctor2.2; simp; apply And.intro ih1 da
    cases ih1
    case app x sp h1 h2 =>
      cases h1
      case _ h1 =>
        apply Or.inl; apply Val.app x (sp ++ [(.term, a)]) _ (Or.inl h1)
        simp; rw [Option.bind_eq_some_iff]
        apply Exists.intro (x, sp); simp [*]
      case _ h1 =>
        simp [OpenVarVal] at h1
        generalize fdef : Γ d@x = f at *
        cases f <;> simp [Frame.is_openm] at h1; case _ T =>
        cases Nat.decLt (sp ++ [(SpineVariant.term, a)]).length T.arity
        case _ h3 =>
          simp at h3; apply Or.inr
          replace h2 := Term.neutral_form_law (Eq.symm h2); subst h2
          have j4 := Judgment.app j1 j2 j3; rw [<-Term.apply_spine_peel_term] at *
          have lem1 := inversion_apply_spine j4
          rcases lem1 with ⟨C, lem1, lem2, lem3⟩
          cases lem2; case _ j5 j6 =>
          rw [fdef] at j6; simp [Frame.get_type] at j6; subst j6
          replace h1 := h1 C (by simp [Frame.get_type])
          replace h1 : C.arity = sp.length + 1 := by omega
          replace dΓ := (dΓ x).1 C B' (sp ++ [(SpineVariant.term, a)]) fdef (by simp; omega) lem1
          rcases dΓ with ⟨t, r, dt⟩
          apply Exists.intro t; apply And.intro r dt
        case _ h3 =>
          simp at h3; apply Or.inl; apply Val.app x (sp ++ [(.term, a)])
          simp; rw [Option.bind_eq_some_iff]
          apply Exists.intro (x, sp); simp [*]
          apply Or.inr; simp [OpenVarVal]; rw [fdef]; simp [Frame.is_openm]
          intro S sh; simp [Frame.get_type] at sh; subst sh
          apply h3
    case choice => simp at df
    case lam C b =>
      apply Or.inr; apply Exists.intro (b β[a])
      apply And.intro; apply RedPlus.one Red.beta
      simp at df; apply Determined.beta _ df.2 da
    all_goals (cases j1)
  case lamt => apply Or.inl; apply Val.lamt
  case appt Γ f A B a B' j1 j2 j3 ih1 ih2 df da dΓ =>
    simp at ih1 h; replace ih1 := ih1 h df dΓ
    rcases ih1 with ⟨ih1⟩ | ⟨f', r, ih1⟩; rotate_left
    apply Or.inr; apply Exists.intro (f' `@t a)
    apply And.intro; apply RedPlus.ctor2_congr1 rfl r
    apply Determined.ctor2.2; simp; apply And.intro ih1 da
    cases ih1
    case app x sp h1 h2 =>
      cases h1
      case _ h1 =>
        apply Or.inl; apply Val.app x (sp ++ [(.type, a)]) _ (Or.inl h1)
        simp; rw [Option.bind_eq_some_iff]
        apply Exists.intro (x, sp); simp [*]
      case _ h1 =>
        simp [OpenVarVal] at h1
        generalize fdef : Γ d@x = f at *
        cases f <;> simp [Frame.is_openm] at h1; case _ T =>
        cases Nat.decLt (sp ++ [(SpineVariant.type, a)]).length T.arity
        case _ h3 =>
          simp at h3; apply Or.inr
          replace h2 := Term.neutral_form_law (Eq.symm h2); subst h2
          have j4 := Judgment.appt j1 j2 j3; rw [<-Term.apply_spine_peel_type] at *
          have lem1 := inversion_apply_spine j4
          rcases lem1 with ⟨C, lem1, lem2, lem3⟩
          cases lem2; case _ j5 j6 =>
          rw [fdef] at j6; simp [Frame.get_type] at j6; subst j6
          replace h1 := h1 C (by simp [Frame.get_type])
          replace h1 : C.arity = sp.length + 1 := by omega
          replace dΓ := (dΓ x).1 C B' (sp ++ [(SpineVariant.type, a)]) fdef (by simp; omega) lem1
          rcases dΓ with ⟨t, r, dt⟩
          apply Exists.intro t; apply And.intro r dt
        case _ h3 =>
          simp at h3; apply Or.inl; apply Val.app x (sp ++ [(.type, a)])
          simp; rw [Option.bind_eq_some_iff]
          apply Exists.intro (x, sp); simp [*]
          apply Or.inr; simp [OpenVarVal]; rw [fdef]; simp [Frame.is_openm]
          intro S sh; simp [Frame.get_type] at sh; subst sh
          apply h3
    case choice => simp at df
    case lamt C b =>
      apply Or.inr; apply Exists.intro (b β[a])
      apply And.intro; apply RedPlus.one Red.betat
      simp at df; apply Determined.beta _ df.2 da
    all_goals (cases j1)
  case cast => sorry
  case refl => sorry
  case sym => sorry
  case seq => sorry
  case appc => sorry
  case arrowc => sorry
  case fst => sorry
  case snd => sorry
  case allc => sorry
  case apptc => sorry
  case empty dt _ => exfalso; apply dt; constructor; simp

theorem determined_progress :
  (∀ x, ¬ Γ.is_type x) ->
  Γ ⊢ t : A ->
  t.Determined Γ.variants ->
  Γ.Determined ->
  Val Γ t ∨ (∃ t', RedPlus Γ t t' ∧ t'.Determined Γ.variants)
:= by
  intro h j dt dΓ
  have lem := determined_progress_lemma h j
  simp at lem; apply lem dt dΓ

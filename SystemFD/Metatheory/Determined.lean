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

set_option maxHeartbeats 5000000

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
def Determined.ite : Term.Determined Γ (.ite p s t e) <->
  Term.Determined Γ p ∧ Term.Determined Γ s ∧ Term.Determined Γ t ∧ Term.Determined Γ e := by
  apply Iff.intro
  · intro h; apply not_contains_variant_ite h
  · intro h1 h2; cases h2
    simp at *
    apply h1.1; assumption
    apply h1.2.1; assumption
    apply h1.2.2.1; assumption
    apply h1.2.2.2; assumption

@[simp]
def Determined.let :
    Term.Determined Γ (.letterm A t b)
    <-> Term.Determined Γ A ∧ Term.Determined Γ t ∧ Term.Determined (.term :: Γ) b := by
  apply Iff.intro
  · intro h; have lem := not_contains_variant_letterm h;
    constructor
    · apply lem.1
    · constructor; apply lem.2.1; apply lem.2.2
  · intro h; cases h; case _ h =>
    cases h; simp at *
    unfold Term.Determined; intro h;
    cases h <;> try (simp at *)
    case _ h' _ _ h => apply h' h
    case _ h' _ h => apply h' h
    case _ h' h => apply h' h

@[simp]
def Determined.bind2 :
  Term.Determined Γ (.bind2 v t1 t2)
  <-> Term.Determined Γ t1 ∧ Term.Determined (bind2_frame_variant v::Γ) t2
:= by
  apply Iff.intro
  · intro h; apply not_contains_variant_bind2 h
  · intro h; rcases h with ⟨h1, h2⟩; intro h3
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
  case letterm Γ A t b T jA jt jb jT _ ih1 ih2  _ dA dt db dΓ =>
    apply Or.inr;
    exists (b β[t]); constructor
    · constructor; constructor
    · apply Determined.beta .term; assumption; assumption
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
  case ite Γ p _ s _ i _ _ e pJ sJ _ iJ vhvp vhvR _ _ _ eJ  _ ih _ _ _ _ h1 h2 h3 h4 h5 =>
    replace ih := ih h; simp at ih
    replace ih := ih h2 h5
    apply Or.inr;
    rcases ih with ⟨ih⟩ | ⟨s', r, ih⟩
    case _ =>
      have lem := canonical_datatype sJ ih vhvR
      cases lem;
      case _ lem =>
        simp [ValidHeadVariable] at vhvp lem
        cases lem; case _ x lem =>
        cases lem; cases vhvp; case _ sctor x' vhvp =>
        cases vhvp; case _ snf pnf pctor =>
        cases snf; case _ sp snf =>
        cases pnf; case _ sp' pnf =>
        cases Nat.decEq x' x
        case _ ne =>
          exists e
          constructor
          · constructor
            apply Red.ite_missed pnf snf
            simp; apply Frame.is_ctor_implies_is_stable_red sctor
            apply Or.inl; assumption
          · assumption
        case _ e =>
          generalize qdef : prefix_equal sp' sp = q at *
          subst e;
          cases q;
          case _ => sorry
          case _ q =>
          exists (i.apply_spine q)
          constructor
          · constructor; apply Red.ite_matched pnf snf (Eq.symm qdef) sctor
          · sorry
          -- apply Red.ite_matched pnf snf _ (by assumption)
      case _ lem =>
       cases lem; case _ lem =>
       cases lem; case _ lem =>
       rw[lem] at h2; simp at h2
    case _ ih =>
      exists (If p ← s' then i else e)
      constructor
      apply RedPlus.ite_congr r
      apply Determined.ite.2
      constructor; assumption
      constructor; assumption
      constructor; assumption
      assumption
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
  case cast Γ t _ _ _ _ tJ cJ _ ih _ d ctxd =>
    replace ih := ih h; simp at ih;
    replace ih := ih d ctxd
    rcases ih with ⟨ih⟩ | ⟨f', r, ih⟩
    apply Or.inr
    · exists t;
      have lem := refl_is_val cJ ih;
      cases lem;
      case _ lem =>
        cases lem; case _ e1 e2 =>
        subst e1; subst e2
        constructor
        · constructor; constructor
        · assumption
      case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ lem =>
        rw[lem] at d; exfalso; simp at d
    · apply Or.inr;
      exists (t ▹ f')
      constructor
      · apply RedPlus.ctor2_congr2; simp; assumption
      · apply Determined.ctor2.2;
        constructor; simp; constructor; assumption; assumption

  case refl => apply Or.inl; apply Val.refl

  case sym Γ t K A _ tJ ih d dΓ =>
    replace ih := ih h; simp at ih
    replace ih := ih d dΓ
    rcases ih with ⟨ih⟩ | ⟨t', r, ih⟩
    · have lem := refl_is_val tJ ih
      cases lem
      · case _ lem => cases lem; case _ e1 e2 =>
        subst e1; subst e2;
        apply Or.inr; exists (refl! K A);
        constructor
        · constructor; constructor
        · assumption
      · case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ lem =>
        exfalso; rw[lem] at d; simp at d
    · apply Or.inr; exists (.ctor1 .sym t');
      constructor
      · apply RedPlus.ctor1_congr; assumption
      · apply Determined.ctor1.2; assumption

  case seq Γ t1 _ _ _ t2 _ t1J t2J ih1 ih2 d1 d2 dΓ =>
    replace ih1 := ih1 h; simp at ih1;
    replace ih1 := ih1 d1 dΓ
    replace ih2 := ih2 h; simp at ih2;
    replace ih2 := ih2 d2 dΓ
    rcases ih2 with ⟨ih2⟩ | ⟨t', r, ih2⟩
    · have lem := refl_is_val t2J ih2
      cases lem
      case _ e =>
        cases e; case _ K A B C e1 e2 =>
        subst e1; subst e2
        rcases ih1 with ⟨ih1⟩ | ⟨t1', r1, ih1⟩
        · have lem := refl_is_val t1J ih1
          cases lem
          case _ e =>
            cases e; case _ e1 e2 =>
            subst e1; subst e2
            apply Or.inr; exists (refl! K A)
            constructor
            · constructor; constructor
            · assumption
          case _ lem =>
            cases lem; case _ lem =>
            cases lem; case _ lem =>
            rw[lem] at d1; simp at d1
        · apply Or.inr; exists (t1' `; refl! K B);
          constructor;
          · apply RedPlus.ctor2_congr1; simp; assumption
          · apply Determined.ctor2.2;
            constructor; simp; constructor; assumption; assumption
      case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ e => rw[e] at d2; simp at d2
    · apply Or.inr; exists (t1 `; t');
      constructor
      · apply RedPlus.ctor2_congr2; simp; assumption
      · apply Determined.ctor2.2
        constructor; simp; constructor; assumption; assumption
  case appc Γ t1 K1 K2 A B t2 C D t1J t2J ih1 ih2 d1 d2 dΓ =>
    replace ih1 := ih1 h; simp at ih1;
    replace ih1 := ih1 d1 dΓ
    replace ih2 := ih2 h; simp at ih2;
    replace ih2 := ih2 d2 dΓ
    rcases ih2 with ⟨ih2⟩ | ⟨t', r, ih2⟩
    · have lem := refl_is_val t2J ih2
      cases lem
      case _ e =>
        cases e; case _ e1 e2 =>
        subst e1; subst e2
        rcases ih1 with ⟨ih1⟩ | ⟨t1', r1, ih1⟩
        · have lem := refl_is_val t1J ih1
          cases lem
          case _ e =>
            cases e; case _ e1 e2 =>
            subst e1; subst e2
            apply Or.inr; exists (refl! K2 (A `@k C))
            constructor
            · constructor; constructor
            · apply Determined.ctor2.2; constructor
              · simp
              · have lem1 := Determined.ctor2.1 d1;
                have lem' := Determined.ctor2.1 lem1.2.1;
                constructor
                apply lem'.2.2
                have lem2 := Determined.ctor2.1 d2
                apply Determined.ctor2.2;
                constructor; simp; constructor; apply lem1.2.2; apply lem2.2.2
          case _ lem =>
            cases lem; case _ lem =>
            cases lem; case _ lem =>
            rw[lem] at d1; simp at d1
        · apply Or.inr; exists (t1' `@c refl! K1 C);
          constructor;
          · apply RedPlus.ctor2_congr1; simp; assumption
          · apply Determined.ctor2.2;
            constructor; simp; constructor; assumption; assumption
      case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ e => rw[e] at d2; simp at d2
    · apply Or.inr; exists (t1 `@c t');
      constructor
      · apply RedPlus.ctor2_congr2; simp; assumption
      · apply Determined.ctor2.2
        constructor; simp; constructor; assumption; assumption
  case arrowc Γ t1 A B t2 C D t1J t2J ih1 ih2 d1 d2 dΓ =>
    replace ih1 := ih1 h; simp at ih1;
    replace ih1 := ih1 d1 dΓ
    have h' : ∀ x : Nat, ¬ (Γ.add .empty).is_type x  := by
      intro x h; simp at h;
      induction x generalizing Γ
      · simp [Frame.is_type] at h; simp [Frame.apply] at h
      case _ h' => simp_all; simp [Frame.apply] at h; unfold Frame.is_type at h'; sorry

    have dΓ' : (Γ.add .empty).Determined := by
      simp; unfold Ctx.Determined;
      intro i
      unfold Ctx.Determined at dΓ

      sorry
    replace ih2 := ih2 h'; simp at ih2;
    replace ih2 := ih2 d2 dΓ'
    rcases ih2 with ⟨ih2⟩ | ⟨t', r, ih2⟩
    · have lem := refl_is_val t2J ih2
      cases lem
      case _ e =>
        cases e; case _ e1 e2 =>
        subst e1; subst e2
        rcases ih1 with ⟨ih1⟩ | ⟨t1', r1, ih1⟩
        · have lem := refl_is_val t1J ih1
          cases lem
          case _ e =>
            cases e; case _ e1 e2 =>
            subst e1; subst e2
            apply Or.inr; exists (refl! ★ (A -t> C))
            have lem := Determined.ctor2.1 d1;
            constructor
            · constructor; constructor
            · apply Determined.ctor2.2
              constructor
              · simp
              · constructor
                · apply lem.2.1
                · apply Determined.bind2.2; constructor
                  · apply lem.2.2
                  · have lem := Determined.ctor2.1 d2; apply lem.2.2
          case _ lem =>
            cases lem; case _ lem =>
            cases lem; case _ lem =>
            rw[lem] at d1; simp at d1
        · apply Or.inr; exists (t1' -c> refl! ★ C);
          constructor;
          · apply RedPlus.bind2_congr1; simp; assumption
          · apply Determined.bind2.2;
            constructor; assumption; assumption
      case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ e => rw[e] at d2; simp at d2
    · apply Or.inr; exists (t1 -c> t');
      constructor
      · apply RedPlus.bind2_congr2; simp; assumption
      · apply Determined.bind2.2
        constructor; assumption; assumption
  case fst Γ A K1 K2 B t C D AJ BJ tJ ih1 ih2 ih3 d1 d2 dΓ =>
    replace ih3 := ih3 h; simp at ih3
    replace ih3 := ih3 d2 dΓ
    rcases ih3 with ⟨ih3⟩ | ⟨t', r, ih3⟩
    · have lem := refl_is_val tJ ih3
      cases lem
      · case _ lem => cases lem; case _ e1 e2 =>
        subst e1; simp at e2; cases e2; case _ e2 e3 =>
        subst e2; subst e3
        apply Or.inr; exists (refl! (K1 -k> K2) A);
        constructor
        · constructor; constructor
        · apply Determined.ctor2.2; simp;
          have lem := Determined.ctor2.1 d2
          constructor
          · constructor; assumption
            apply lem.2.1
          · replace lem := Determined.ctor2.1 lem.2.2
            apply lem.2.1
      · case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ lem =>
        exfalso; rw[lem] at d2; simp at d2
    · apply Or.inr; exists (.ctor2 .fst K1 t');
      constructor
      · apply RedPlus.ctor2_congr2; simp; assumption
      · apply Determined.ctor2.2; simp; constructor; assumption; assumption
  case snd Γ K1 C D t K2 A B _ CJ DJ tJ ih1 ih2 ih3 ih4 d1 d2 dΓ =>
    replace ih4 := ih4 h; simp at ih4
    replace ih4 := ih4 d2 dΓ
    rcases ih4 with ⟨ih4⟩ | ⟨t', r, ih4⟩
    · have lem := refl_is_val tJ ih4
      cases lem
      · case _ lem => cases lem; case _ e1 e2 =>
        subst e1; simp at e2; cases e2; case _ e2 e3 =>
        subst e2; subst e3
        apply Or.inr; exists (refl! K1 C)
        constructor
        · constructor; constructor
        · apply Determined.ctor2.2; simp; constructor
          · assumption
          · have lem := Determined.ctor2.1 d2;
            replace lem := Determined.ctor2.1 lem.2.2; apply lem.2.2
      · case _ lem =>
        cases lem; case _ lem =>
        cases lem; case _ lem =>
        exfalso; rw[lem] at d2; simp at d2
    · apply Or.inr; exists (.ctor2 .snd K1 t');
      constructor
      · apply RedPlus.ctor2_congr2; simp; assumption
      · apply Determined.ctor2.2; simp; constructor; assumption; assumption

  case allc =>
    sorry
  case apptc =>
    sorry
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

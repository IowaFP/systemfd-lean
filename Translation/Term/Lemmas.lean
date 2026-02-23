import Core.Ty
import Core.Term
import Core.Metatheory.Determined
import Surface.Ty
import Surface.Term

import Translation.Ty
import Translation.Term

import Translation.Ty.Lemmas

import Translation.Ty
import Translation.Term
import Translation.Global
import Core.Typing
import Core.Metatheory.Inversion

import Surface.Typing
import Surface.Metatheory.Inversion

open LeanSubst

def Surface.TyEnv.translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Surface.TyEnv) : Option (Core.TyEnv) := Γ.mapM (·.translate G Δ )


theorem Translation.KindEnv.lift_sound  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv} {K : Surface.Kind} {K'}:
  Δ.translate = Δ' ->
  K.translate = K' ->
  Surface.KindEnv.translate (K::Δ) = K' :: Δ':= by
intro h1 h2
rw[Surface.KindEnv.translate, List.map_cons]
rw[Surface.KindEnv.translate] at h1
simp [h1, h2]

theorem Translation.TyEnv.kindenv_lift_sound
  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv}
  {Γ : Surface.TyEnv} {Γ' : Core.TyEnv}
  {K : Surface.Kind} {K' : Core.Kind}:
  Γ.translate G' Δ' = some Γ' ->
  K.translate = K' ->
  Surface.KindEnv.translate (K::Δ) = (K'::Δ') ->
  Surface.TyEnv.translate G' (K'::Δ') (Γ.map (·[+1])) = some (Γ'.map (·[+1]))
   := by
intro h1 h2 h3
unfold Surface.TyEnv.translate;
sorry


theorem Translation.TyEnv.lift_sound
  {G : Surface.GlobalEnv} {G' : Core.GlobalEnv}
  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv}
  {Γ : Surface.TyEnv} {Γ' : Core.TyEnv}
  {A : Surface.Ty} {A' : Core.Ty} :
  Γ.translate G' Δ' = some Γ' ->
  G&Δ ⊢s A : .base b ->
  A.translate G' Δ' = some A' ->
  Surface.TyEnv.translate G' Δ' (A :: Γ)= some (A'::Γ') := by
intro h1 j h2
simp [Surface.TyEnv.translate, Surface.TyEnv.mapM, List.mapM_cons, bind, instMonadOption, Option.bind_eq_some_iff];
constructor
· assumption
· apply h1


theorem Translation.TyEnv.sound {G : Core.GlobalEnv} {Δ : Core.KindEnv} {Γ : Surface.TyEnv} {Γ' : Core.TyEnv} :
  Γ.translate G Δ = some Γ' ->
  (∀ (i : Nat) (T : Surface.Ty),
     (Γ[i]? = some T) -> ∃ T', ((Γ'[i]? = some T') ∧ T.translate G Δ = some T')) := by
intro h1 i T h2;
induction Γ using List.mapM'.induct generalizing G Δ Γ' i <;> simp [Surface.TyEnv] at h2
case _ => cases h2
case _ hT Γ ih =>
  simp [Surface.TyEnv.translate, Surface.TyEnv.mapM, List.mapM_cons] at *
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨T', h1, h2⟩
  rw[Option.bind_eq_some_iff] at h2
  rcases h2 with ⟨Γ', h3, h4⟩
  cases h4
  cases i <;> simp [Surface.TyEnv, Surface.inst_getElem?_TyEnv, Core.TyEnv, Core.inst_getElem?_TyEnv,] at *
  case zero => subst h2; assumption
  case succ n =>
    replace ih := @ih G Δ Γ' h3 n h2
    rcases ih with ⟨T', h4, h5⟩
    exists T'



theorem Translation.GlobalEnv.sound {G : Surface.GlobalEnv} :
  ⊢s G ->
  G.translate = some G' ->
  (∀ (x : String) (T : Surface.Ty) (Δ : Core.KindEnv),
    (Surface.lookup_type G x = some T) ->
    ∃ T' b, (Core.lookup_type G' x = some T' ∧ T.translate G' Δ = some T' ∧ G'&Δ ⊢ T' : .base b)) := by
intro h1 i K h2; sorry



theorem Translation.Term.Sound (G : Surface.GlobalEnv) :
  ⊢s G ->
  G&Δ,Γ ⊢s t : T ->


  G.translate = some G' ->
  ⊢ G' ->
  Δ.translate = Δ' ->
  Γ.translate G' Δ' = some Γ' ->

  ∃ T', (T.translate G' Δ' = some T' ∧
  ∃ t', t.translate G' Δ' Γ' = some t' ∧
  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T') := by
intro wf j h1 wfc h2 h3
induction j generalizing Δ' Γ' <;> simp at *
case var Γ x T Δ b h jk =>
  have lem := Translation.TyEnv.sound h3 x T h
  rcases lem with ⟨T', h4, h5⟩
  replace jk := Translation.Ty.sound wf ⟨jk, h1 , h2⟩
  rcases jk with ⟨K', T', h6, h7, h8⟩
  have h6' := Translation.Kind.sound_base (b := b);
  rcases h6' with ⟨b', h6'⟩;
  rw[h6'] at h6; subst h6
  rw[h7] at h5; cases h5
  exists T'
  constructor
  · assumption
  · constructor
    · unfold Core.Term.Determined; apply Core.VariantMissing.var
    · apply Core.Typing.var; repeat assumption
case global x T Δ b Γ h4 j =>
  have lem := Translation.GlobalEnv.sound wf h1 x T Δ' h4
  rcases lem with ⟨T', h4, h5, h6, h7⟩
  exists T'
  constructor
  · assumption
  · constructor
    unfold Core.Term.Determined; apply Core.VariantMissing.global
    apply Core.Typing.global;
    assumption
    assumption
case lam Δ A b1 Γ t B j1 j2 ih =>
  have lemA := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lemA with ⟨aK', A', h4a, h5a, h6a⟩
  have lem := Translation.TyEnv.lift_sound h3 j1 h5a
  replace ih := @ih _ (A' :: Γ') h2  lem
  rcases ih with ⟨B', h8, t', h10, h11, h12⟩
  have lem := Core.Typing.well_typed_terms_have_base_kinds wfc h12
  rcases lem with ⟨_, jB'⟩
  exists (A' -:> B'); rw[Option.bind_eq_some_iff]
  apply And.intro
  · exists A'
    apply And.intro
    · assumption
    · rw[Option.bind_eq_some_iff]; exists B'
  · exists (λ[A']t')
    rw[Option.bind_eq_some_iff];
    apply And.intro
    exists A'; apply And.intro; assumption; rw[Option.bind_eq_some_iff]; exists t'
    have h6' := Translation.Kind.sound_base (b := b1)
    rcases h6' with ⟨b1', h6'⟩
    subst aK'; rw[h6'] at h6a
    apply And.intro
    · apply Core.Term.Determined.lam; assumption
    · apply Core.Typing.lam (b := b1')
      assumption
      assumption
case lamt Δ K P t Γ j1 j2 ih =>
  have lem := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lem with ⟨K', T', h4, h5, h6⟩
  simp at h5; rw[Option.bind_eq_some_iff] at h5;
  rcases h5 with ⟨P', h7, h8⟩
  cases h8; simp at h4; subst K'
  exists (∀[K.translate]P')
  rw[Option.bind_eq_some_iff]
  constructor
  · simp; assumption
  · have lemK := Translation.KindEnv.lift_sound (K := K) (K' := K.translate) h2 rfl
    have lemT := Translation.TyEnv.kindenv_lift_sound (K := K) (K' := K.translate) (Δ := Δ) (Δ' := Δ') h3 rfl lemK
    simp at lemT ih;
    replace ih := @ih (K.translate :: Δ') (Γ'.map (·[+1])) lemK lemT
    rcases ih with ⟨P', h8, t', h9, h10, h11⟩
    rw[h7] at h8; cases h8
    exists (Λ[K.translate]t');
    apply And.intro
    · rw[Option.bind_eq_some_iff]; exists t'
    · apply And.intro
      · apply Core.Term.Determined.lamt; assumption
      · apply Core.Typing.lamt; assumption; assumption
case app Δ A Γ f B a j1 j2 j3 ih1 ih2 =>
  have lem := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lem with ⟨K', A', e1, e2, e3⟩
  simp at e1; subst K'
  replace ih1 := ih1 h2 h3
  rcases ih1 with ⟨T', ih1⟩
  rw[Option.bind_eq_some_iff] at ih1
  rcases ih1 with ⟨h4, f', h5, h6, h7⟩
  rcases h4 with ⟨A', h8, h9⟩
  rw[Option.bind_eq_some_iff] at h9
  rcases h9 with ⟨B', h9, h10⟩
  cases h10

  replace ih2 := ih2 h2 h3
  rcases ih2 with ⟨A', h10, a', h11, h12, h13⟩

  rw[h8] at h10; cases h10
  rw[h8] at e2; cases e2
  exists B'
  apply And.intro
  · assumption
  · exists (f' • a')
    rw[Option.bind_eq_some_iff];
    apply And.intro
    · exists f'
      apply And.intro
      · assumption
      · rw[Option.bind_eq_some_iff]; exists a'
    · apply And.intro
      · apply Core.Term.Determined.app; assumption; assumption
      · apply Core.Typing.app;
        assumption
        assumption
        assumption


case appt Δ Γ f K P a P' j1 j2 e ih =>
  replace ih := ih h2 h3
  rcases ih with ⟨T', h4, h5⟩
  rw[Option.bind_eq_some_iff] at h4
  rcases h4 with ⟨Pk', h4, h6⟩
  cases h6
  rcases h5 with ⟨f', h6, h7, h8⟩

  have lem := Translation.Ty.sound wf ⟨j2, h1, h2⟩
  rcases lem with ⟨K', A', h9, h10, h11⟩
  subst K'
  exists Pk'[su A' :: +0:_]
  apply And.intro
  · have lem := Surface.Typing.well_typed_terms_have_base_kinds wf j1;
    rcases lem with ⟨_, lem⟩
    cases lem; case _ jp =>
    have lem := Translation.KindEnv.lift_sound (K := K) (K' := K.translate) h2 rfl
    replace lem := Translation.Ty.sound wf ⟨jp, h1, lem⟩
    rcases lem with ⟨bk, Pk', e1, e2, e3⟩
    simp at e1; subst e1
    rw[h4] at e2; cases e2
    have lem := Translation.Ty.beta (P' := Pk') (K' := K.translate) wf j2 jp h1 h2 rfl h10 h4
    subst e
    assumption

  exists f' •[ A']
  · rw[Option.bind_eq_some_iff]
    apply And.intro
    · exists f'; apply And.intro
      · assumption
      · rw[Option.bind_eq_some_iff]; exists A'
    · apply And.intro
      · apply Core.Term.Determined.appt; assumption
      · apply Core.Typing.appt
        assumption
        assumption
        rfl

case mtch n Δ Γ s R c T CTy PTy pats cs sj vhvR cj vhvps patsj stmPTys csj ptms ih1 ih2 ih3 ih4 =>
  replace ih1 := ih1 h2 h3
  rcases ih1 with ⟨R', ih1, s', ih1b, ih1c, ih1d⟩
  replace ih2 := ih2 h2 h3
  rcases ih2 with ⟨T', ih2, c', ih2b, ih2c, ih2d⟩

  replace ih3 : ∃ (PTy' : Vect n Core.Ty),
          (∀ (i : Fin n), Surface.Ty.translate G' Δ' (PTy i) = some (PTy' i)) ∧
          ∃ (pats' : Vect n Core.Term),
          (∀ i, Surface.Term.translate G' Δ' Γ' (pats i) = some (pats' i)) ∧
          (∀ i, (pats' i).Determined) ∧
          (∀ i, G'&Δ',Γ' ⊢ (pats' i) : (PTy' i)) := by



    sorry
  replace ih4 : ∃ (CTy' : Vect n Core.Ty),
          (∀ (i : Fin n), Surface.Ty.translate G' Δ' (CTy i) = some (CTy' i)) ∧
          ∃ (cs' : Vect n Core.Term),
          (∀ i, Surface.Term.translate G' Δ' Γ' (cs i) = some (cs' i)) ∧
          (∀ i, (cs' i).Determined) ∧
          (∀ i, G'&Δ',Γ' ⊢ (cs' i) : (CTy' i)) := by
    sorry

  rcases ih3 with ⟨PTy', ih3a, ps', ih3b, ih3c, ih3d⟩
  rcases ih4 with ⟨CTy', ih4a, cs', ih5b, ih5c, ih5d⟩

  exists T'
  apply And.intro
  · assumption
  · exists (match! s' ps' cs' c')
    rw[Option.bind_eq_some_iff];
    apply And.intro
    · exists s';
      apply And.intro
      · assumption
      · rw[Option.bind_eq_some_iff];
        exists (λ i => ps' i)
        rw[Option.bind_eq_some_iff]
        apply And.intro
        · unfold Vect.seq; simp;
          split
          · case _ ph _ =>
             simp at *; cases ph;
             case _ i ih3b' _ =>
             replace ih3b := ih3b i
             rw[ih3b] at ih3b'; simp at ih3b'
          · simp; funext; case _ x =>
            replace ih3b := ih3b x;
            unfold Option.get;
            split; case _ e1 e2 e3 e4 e5 e6 e7 =>
            simp at *; rw[ih3b] at e6; cases e6; rfl
        · exists (λ i => cs' i)
          rw[Option.bind_eq_some_iff]
          apply And.intro
          · unfold Vect.seq; simp
            split;
            · case _ ph _ =>
              simp at *; cases ph;
              case _ i ih5b' _ =>
              replace ih5b := ih5b i
              rw[ih5b] at ih5b'; simp at ih5b'
            · simp; funext; case _ x =>
              replace ih5b := ih5b x;
              unfold Option.get;
              split; case _ e1 e2 e3 e4 e5 e6 e7 =>
              simp at *; rw[ih5b] at e1; rw[ih5b] at e6; cases e6; rfl
          · exists c'
    · apply And.intro
      · apply Core.Term.Determined.match; repeat assumption
      · apply Core.Typing.mtch (CTy := CTy') (PTy := PTy') (pats := ps') (cs := cs')
        assumption
        sorry
        assumption
        sorry
        assumption
        sorry
        assumption
        sorry


theorem quantifier_magic {Δ : Surface.KindEnv} {Γ : Surface.TyEnv} {PTy : Fin n -> Surface.Ty} {pats : Vect n Surface.Term} :
  Δ.translate = Δ' ->
  Surface.TyEnv.translate G' Δ' Γ = some Γ' ->
  (∀ (i : Fin n) {Δ' : Core.KindEnv} {Γ' : Core.TyEnv},
    Δ.translate = Δ' →
      Surface.TyEnv.translate G' Δ' Γ = some Γ' →
        ∃ T',
          Surface.Ty.translate G' Δ' (PTy i) = some T' ∧
            ∃ t', Surface.Term.translate G' Δ' Γ' (pats i) = some t' ∧ t'.Determined ∧ G'&Δ',Γ' ⊢ t' : T') ->

 (∃ (PTy' : Fin n -> Core.Ty),
          (∀ (i : Fin n),
            Δ.translate = Δ' →
            Surface.TyEnv.translate G' Δ' Γ = some Γ' →
            Surface.Ty.translate G' Δ' (PTy i) = some (PTy' i))) ∧
 (∃ (pats' : Vect n Core.Term),
       Δ.translate = Δ' →
       Surface.TyEnv.translate G' Δ' Γ = some Γ' →
   (∀ i, Surface.Term.translate G' Δ' Γ' (pats i) = some (pats' i))) ∧
 (∃ (pats' : Vect n Core.Term), (∀ i, (pats' i).Determined)) ∧
 (∃ (PTy' : Fin n -> Core.Ty), ∃ (pats' : Vect n Core.Term),
      Δ.translate = Δ' →
      Surface.TyEnv.translate G' Δ' Γ = some Γ' →
   (∀ i, G'&Δ',Γ' ⊢ (pats' i) : (PTy' i))) := by
intro h1 h2 h
-- have lem :
--   ∀ (i : Fin n) {Δ' : Core.KindEnv} {Γ' : Core.TyEnv},
--     Δ.translate = Δ' ->
--     Surface.TyEnv.translate G' Δ' Γ = some Γ' ->
--      (∃ T',
--       Δ.translate = Δ' →
--       Surface.TyEnv.translate G' Δ' Γ = some Γ' →
--       Surface.Ty.translate G' Δ' (PTy i) = some T') ∧
--      (∃ pats',
--        Δ.translate = Δ' →
--        Surface.TyEnv.translate G' Δ' Γ = some Γ' →
--        Surface.Term.translate G' Δ' Γ' (pats i) = some pats') ∧
--      (∃ pats' : Vect n Core.Term, (pats' i).Determined) ∧
--      (∃ T', ∃ pats' : Vect n Core.Term,
--         Δ.translate = Δ' →
--         Surface.TyEnv.translate G' Δ' Γ = some Γ' →
--        G'&Δ',Γ' ⊢ (pats' i) : T') := by
--   intro i Δ' Γ' h1 h2
--   replace h := @h i Δ' Γ' h1 h2
--   rcases h with ⟨T', e1, pats', e2, e3, e4⟩
--   apply And.intro
--   exists T'; intros; assumption
--   apply And.intro
--   exists pats'; intros; assumption
--   apply And.intro
--   sorry
--   sorry
apply And.intro
· sorry
· sorry

-- constructor
-- apply And.intro
-- · intro i
--   replace h := @h i _ _ h1 h2
--   rcases h with ⟨T', h1, pat, h3, h4⟩



--   sorry
-- · sorry
-- (intro i
--  replace h := @h i _ _ h1 h2
--  sorry)

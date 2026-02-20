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
import Surface.Typing


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


theorem Translation.TyEnv.sound {G : Core.GlobalEnv} {Δ : Core.KindEnv} {Γ : Surface.TyEnv} {Γ' : Core.TyEnv} :
  Γ.translate G Δ = some Γ' ->
  (∀ (i : Nat) (T : Surface.Ty),
     (Γ[i]? = some T) -> ∃ T', ((Γ'[i]? = some T') ∧ T.translate G Δ = some T')) := by
intro h1 i K h2;

sorry


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
  Δ.translate = Δ' ->
  Γ.translate G' Δ' = some Γ' ->

  ∃ T' t', (T.translate G' Δ' = some T' ∧
  t.translate G' Δ' Γ' = some t' ∧
  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T') := by
intro wf j h1 h2 h3
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

case lam Δ A b1 B b2 Γ t j1 j2 j3 ih =>
  have lemA := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lemA with ⟨aK', A', h4a, h5a, h6a⟩
  have lemB := Translation.Ty.sound wf ⟨j2, h1, h2⟩
  rcases lemB with ⟨bK', B', h4b, h5b, h6b⟩
  have h6' := Translation.Kind.sound_base (b := b1)
  rcases h6' with ⟨b1', h6'⟩
  have h6'' := Translation.Kind.sound_base (b := b2)
  rcases h6'' with ⟨b2', h6''⟩
  rw[h6'] at h4a; subst h4a; clear h6'
  rw[h6''] at h4b; subst h4b; clear h6''
  exists (A' -:> B'); rw[Option.bind_eq_some_iff]
  constructor
  · exists A'; constructor; assumption;
    rw[Option.bind_eq_some_iff]; simp; assumption
  · have lem : Surface.TyEnv.translate G' Δ' (A :: Γ) = some (A' :: Γ') := by
      rw [Surface.TyEnv.translate]; unfold Surface.TyEnv.mapM; rw[<-List.mapM'_eq_mapM]
      simp [bind, instMonadOption, Option.bind_eq_some_iff];
      constructor; assumption; rw[Surface.TyEnv.translate] at h3; rw[List.mapM'_eq_mapM]
      apply h3;
    replace ih := @ih Δ' (A' :: Γ') h2 lem
    rcases ih with ⟨B', h7, t', h9, h10, h11⟩
    exists λ[A']t'; rw[Option.bind_eq_some_iff];
    constructor;
    · exists A'; constructor; assumption;
      rw[Option.bind_eq_some_iff]; exists t'
    · constructor
      · constructor; assumption
      · rw[h5b] at h7; cases h7;
        apply Core.Typing.lam; assumption; assumption
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
  · replace ih := @ih (K.translate :: Δ') (Γ'.map (·[+1]))
    sorry
case app =>
  sorry
case appt =>
  sorry
case mtch => sorry

import Translation.Ty
import Translation.Global

import Core.Typing
import Surface.Typing
import Surface.Metatheory.Inversion
import Translation.Rename

open LeanSubst

-- Translation preservies kinding relation

theorem Translation.KindEnv.sound {Δ : Surface.KindEnv} {Δ' : Core.KindEnv} :
  Δ.translate = Δ' ->
  (∀ (i : Nat) (K : Surface.Kind),
     (Δ[i]? = some K) -> ∃ K', ((Δ'[i]? = some K') ∧ K.translate = K')) := by
intro h1 i K h2; simp at *
unfold Surface.KindEnv.translate at h1
have lem := List.map_eq_iff.1 h1 i; simp [Surface.inst_getElem?_KindEnv] at *; rw[h2] at lem; simp at lem
assumption

theorem Translation.Kind.sound_base (b : Surface.BaseKind):
  ∃ b', (Surface.Kind.base b).translate = .base b' := by
cases b <;> simp at *
all_goals (subst K'; simp)

theorem Translation.Kind.sound_arrow {b1 b2 : Surface.Kind}:
  ∃ b1' b2', (Surface.Kind.arrow b1 b2).translate = .arrow b1' b2' := by simp

theorem Translation.GlobalEnv.lookup_kind_sound :
  G.translate = some G' ->
  Surface.lookup_kind G x = some K ->
  Core.lookup_kind G' x = some K'  := by
intro h1 h2
sorry


theorem Translation.Ty.sound :
  ⊢s G ->
  G&Δ ⊢s T : K ∧
  G.translate = some G' ∧
  Δ.translate = Δ'  ->

  ∃ K' T', K.translate = K' ∧
  T.translate = T' ∧
  G'&Δ' ⊢ T' : K' := by
intro wf j;
rcases j with ⟨j, h1, h2⟩
induction j generalizing Δ' <;> simp at *
case var Δ i K j =>
  replace j2 := Translation.KindEnv.sound h2 i K j
  rcases j2 with ⟨K', j', t⟩; rw[<-t] at j'
  constructor; assumption
case global x K Δ h3 =>
  have lem := Translation.GlobalEnv.lookup_kind_sound (K' := K.translate) h1 h3
  apply Core.Kinding.global
  apply lem
case all K Δ P j ih =>
  apply Core.Kinding.all
  rw[Surface.KindEnv.translate, List.map_cons] at ih
  subst Δ'; apply ih

case arrow b1 _ b2 _ _ ih1 ih2 =>
  subst h2
  replace b1 := Translation.Kind.sound_base b1
  rcases b1 with ⟨b1k, b1⟩
  rw[b1] at ih1
  replace b2 := Translation.Kind.sound_base b2
  rcases b2 with ⟨b2k, b2⟩
  rw[b2] at ih2
  apply Core.Kinding.arrow ih1 ih2

case app ih1 ih2 =>
  subst h2; apply Core.Kinding.app ih1 ih2

theorem Translation.Ty.beta {a P: Surface.Ty}:
  a.translate = a' ->
  P.translate = P' ->

  (P[su a :: +0 :_]).translate = (P'[su a' :: +0 :_]) := by
intro h1 h2
generalize σdef : ((su a :: +0 :_)) = σ at *
generalize σ'def : ((su a' :: +0 :_)) = σ' at *
have σe : σ' = Subst.Surface.Ty.translate σ := by
  funext; case _ x =>
  cases x <;> simp at *
  rw[<-σ'def]; simp; rw[<-σdef]; simp; apply Eq.symm h1
  rw[<-σ'def]; rw[<-σdef]; simp
rw[σe]
apply Translation.Ty.Subst σ h2

theorem Translation.Ty.Spine
  {t : Surface.Ty} {t' : Core.Ty} :
  t.spine = some (x, sp) ->
  t.translate = t' ->
  ∃ sp', t'.spine = .some (x, sp') := by
intro h1 h5
induction t using Surface.Ty.spine.induct generalizing x sp t' <;> simp [Surface.Ty.spine] at *
case _ => exists []; rw[<-h5]; cases h1.1; cases h1.2; simp [Core.Ty.spine]
case _ f a ih =>
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨fsf, h1, h8⟩
  cases h8
  generalize fdef : f.translate = f' at *
  generalize adef : a.translate = a' at *
  replace ih := @ih fsf.1 fsf.2 h1
  rcases ih with ⟨f'sp, ih⟩
  exists (f'sp ++ [a']); subst h5
  simp; apply ih

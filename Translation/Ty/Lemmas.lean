import Translation.Ty
import Translation.Entry
import Translation.Global

import Core.Typing
import Surface.Typing
import Core.Metatheory.GlobalWf
import Translation.Rename

open LeanSubst

-- Translation preservies kinding relation

theorem Translation.GlobalEnv.lookup_none_sound x :
  Surface.Global.Elab G G' ->
  Surface.lookup x G = none ->
  Core.lookup x G' = none := by
intro h1 h2
induction h1 generalizing x <;> simp [Surface.lookup, Core.lookup] at *
case defn x' _ _ _ h1 ih =>
  split at h2
  case _ e => subst e; cases h2
  case _ e =>
    split
    exfalso; contradiction
    apply ih _ h2
case data => sorry
case classDecl => sorry

theorem Translation.GlobalEnv.lookup_different_impossible x :
  Surface.Global.Elab G G' ->
  Surface.lookup x G = none ->
  Core.lookup x G' = some e ->
  False
:= by
  intro h1 h2 h3
  have lem := Translation.GlobalEnv.lookup_none_sound x h1 h2
  rw[lem] at h3; cases h3


-- theorem Translation.GlobalEnv.lookup_entry_data x :
--   Surface.Global.Elab G G' ->
--   Surface.lookup x G = some en ->
--   Core.lookup x G' = .some en.translate := by
-- intro h1 h2
-- fun_induction Surface.GlobalEnv.translate generalizing G' <;> simp [Surface.lookup] at *
-- case _ => sorry
-- split at h2;
-- case isTrue =>
--   subst G';
--   simp [gs', g'] at *
--   subst x; subst en; simp [Core.lookup, Surface.Entry.translate];
--   cases g; simp at *; unfold Surface.Ty.translate_ctors; simp
-- case isFalse =>
--   replace h2 := Core.EntryWf.from_lookup_vec1 h2
--   cases h2
--   case inl h2 =>
--     rcases h2 with ⟨i, h2⟩
--     simp at h2; rcases h2 with ⟨e, h2⟩; subst e; subst en;
--     subst G'; subst g'; subst gs'; simp [Core.lookup]at *;
--     split
--     · contradiction
--     · sorry
--   case inr h =>
--     replace h1 := h1 h; subst G'; simp [g', Core.lookup];
--     split <;> simp at *
--     · contradiction
--     · rw[h1]; apply Core.EntryWf.from_lookup_vec3;
--       intro i; split  <;> simp at *
--       simp [Surface.Ty.translate_ctors] at *; subst x; sorry



theorem Translation.GlobalEnv.lookup_kind_sound :
  Surface.Global.Elab G G' ->
  Surface.lookup_kind G x = some K ->
  Core.lookup_kind G' x = some K.translate  := by
intro h1 h2

sorry


theorem Translation.Entry.is_data_sound x :
  Surface.is_data G x ->
  Surface.Global.Elab G G' ->
  Core.is_data G' x := by
intro h1 h2
-- fun_induction Surface.GlobalEnv.translate generalizing G' <;> simp [Surface.is_data, Surface.lookup] at *
-- case _  =>
  -- cases wf; case _ wfgs wfg =>
  -- subst G'; subst gs'; subst g' <;> simp at *
  -- replace ih := ih wfgs
  -- split at h1
  -- case isTrue =>
  --   subst x; simp at h1; simp [Core.is_data, Core.lookup, Core.Entry.is_data]
  -- case isFalse =>
  --   generalize zdef : Vect.fold (Surface.lookup x gs) Option.or (fun i =>
  --         if x = (g.4 i).fst then some (Surface.Entry.ctor (g.4 i).fst (↑i) (g.4 i).snd) else none) = z at *
  --   cases z <;> simp at *
  --   have lem := Core.EntryWf.from_lookup_vec1 zdef
  --   rcases lem with ⟨i, lem⟩
  --   simp at lem; rcases lem with ⟨e, lem⟩; subst x;
  --   sorry
sorry


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


theorem Translation.Ty.sound :
  G&Δ ⊢s T : K ->
  Surface.Global.Elab G G' ->

  G'&⟦Δ⟧ ⊢ ⟦T⟧ : ⟦K⟧ := by
intro j j0;
induction j <;> simp at *
case var Δ i K j =>
  replace j2 := Translation.KindEnv.sound rfl i K j
  rcases j2 with ⟨K', j', t⟩; rw[<-t] at j'
  constructor; assumption
case global x K Δ h3 =>
  have lem := Translation.GlobalEnv.lookup_kind_sound j0 h3
  apply Core.Kinding.global
  apply lem
case all K Δ P j ih =>
  apply Core.Kinding.all
  rw[Surface.KindEnv.translate, List.map_cons] at ih
  apply ih

case arrow b _ _ ih1 ih2 =>
  replace b' := Translation.Kind.sound_base b
  rcases b' with ⟨b2k, b'⟩
  rw[b'] at ih2
  apply Core.Kinding.arrow ih1 ih2

case «then» b _ _ ih1 ih2 =>
  replace b' := Translation.Kind.sound_base b
  rcases b' with ⟨b2k, b'⟩
  rw[b'] at ih2
  apply Core.Kinding.arrow ih1 ih2

case app ih1 ih2 => apply Core.Kinding.app ih1 ih2


theorem Translation.Ty.beta {a P: Surface.Ty}:
  (P[su a :: +0 :_]).translate = (⟦P⟧[su ⟦a⟧ :: +0 :_]) := by
generalize σdef : ((su a :: +0 :_)) = σ at *
generalize σ'def : ((su ⟦a⟧ :: +0 :_)) = σ' at *
have σe : σ' = Subst.Surface.Ty.translate σ := by
  funext; case _ x =>
  cases x <;> simp at *
  rw[<-σ'def]; simp; rw[<-σdef]; simp;
  rw[<-σ'def]; rw[<-σdef]; simp
rw[σe]
apply Translation.Ty.Subst σ
rfl

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

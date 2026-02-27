import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas
import Translation.Global

theorem Translation.Global.is_data_sound x :
  ⊢s G ->
  G.translate = some G' ->
  Surface.is_data G x ->
  Core.is_data G' x := by sorry

theorem Translation.Ty.valid_ctor_ty_sound {G : Core.GlobalEnv} :
  Core.is_valid_ctor_ty G T == some x -> Core.ValidCtor G x T := by
intro h
fun_induction Core.is_valid_ctor_ty <;> simp at *
case _ ih => replace ih := ih h; apply Core.ValidCtor.all ih
case _ ih => replace ih := ih h; apply Core.ValidCtor.arrow ih
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨tnf, h1, h2⟩;
  simp at h2; rcases h2 with ⟨h2, e⟩; subst x
  apply Core.ValidCtor.base; apply h1; apply h2

theorem Translation.Ty.valid_ctor_ty_sound' {G : Surface.GlobalEnv} :
  Surface.is_valid_ctor_ty G T == some x -> Surface.ValidCtor G x T := by
intro h
fun_induction Surface.is_valid_ctor_ty <;> simp at *
case _ ih => replace ih := ih h; apply Surface.ValidCtor.all ih
case _ ih => replace ih := ih h; apply Surface.ValidCtor.arrow ih
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨tnf, h1, h2⟩;
  simp at h2; rcases h2 with ⟨h2, e⟩; subst x
  apply Surface.ValidCtor.base; apply h1; apply h2

theorem Translation.Ty.ValidCtor :
  ⊢s G ->
  G.translate = some G' ->
  Surface.ValidCtor G x T -> Core.ValidCtor G' x ⟦T⟧ := by
intro wf gt h; induction h <;> simp at *
case base h1 h2 =>
  replace lem := Translation.Ty.Spine h1 rfl
  rcases lem with ⟨_, lem⟩
  constructor; assumption; apply Translation.Global.is_data_sound x wf gt h2
case all ih => apply Core.ValidCtor.all ih
case arrow ih => apply Core.ValidCtor.arrow ih

-- theorem Core.Ty.ValidCtorThenDatatype:
--   Core.ValidCtor G x T ->

theorem Translation.Global.empty_data_wkn {G : Surface.GlobalEnv} {G' : Core.GlobalEnv} (x : String) (K : Surface.Kind) :
  G.translate = some G' ->
  Surface.GlobalEnv.translate (.data x K Vect.nil :: G) = some (.data 0 x ⟦K⟧ Vect.nil :: G') := by
intro h; simp [Surface.GlobalEnv.translate]
rw[Option.bind_eq_some_iff]; exists G'

theorem Surface.GlobalEnvWf.empty_data_wkn x K :
  ⊢s G -> lookup x G = none ->
  ⊢s (Surface.Global.data x K Vect.nil :: G) := by
 intro wf lk; apply ListGlobalWf.cons
 · apply GlobalWf.data <;> try simp at *
   apply Vect.nil
   apply lk
 · assumption


theorem Translation.Ty.check_valid_ctors_sound ctors :
  (∀ (i : Fin n) (y : String) (T : Surface.Ty),
    ctors i = (y, T) →
      (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : Surface.Kind.base b`★ ∧
        Surface.ValidCtor (Surface.Global.data x K Vect.nil :: G) x T ∧ x ≠ y ∧ Surface.lookup y G = none) ->
  Core.Ty.check_ctor_tys x (Core.Global.data 0 x ⟦K⟧ Vect.nil :: G') (Surface.Ty.translate_ctors ctors) = some ()
:= by
intro h
unfold Core.Ty.check_ctor_tys
simp;
sorry



theorem Translation.GlobalWf.sound {G : Surface.GlobalEnv} {g : Surface.Global}:
  ⊢s G ->
  Surface.GlobalWf G g ->
  G.translate = some G' ->
  (∀ x, Surface.lookup x G = none -> Core.lookup x G' = none) ->
  ⊢ G' ->
 ∃ g',
    g.translate G' = some g'  ∧
    Core.GlobalWf G' g' := by
intro wf h1 h2 h3 wfc; induction g <;> simp at *
cases h1
case _ n x K ctors cns lk cnsdef ctor_trans =>
let ctors' : Vect n (String × Core.Ty) := Surface.Ty.translate_ctors ctors
exists Core.Global.data n x ⟦K⟧ ctors'
rw[Option.bind_eq_some_iff];
apply And.intro
· exists ()
  apply And.intro
  · sorry
  · simp; unfold ctors'; simp;
. apply Core.GlobalWf.data
  · intro i y T e;
    replace ctor_trans := ctor_trans i (ctors i).fst (ctors i).snd rfl;
    rcases ctor_trans with ⟨k1, k2, k3, k4⟩
    simp [ctors'] at e; rcases e with ⟨e1, e2⟩;
    have lemG := Translation.Global.empty_data_wkn x K h2
    have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
    have lem := Translation.Ty.sound wfG (G := .data x K Vect.nil :: G) ⟨k1,lemG, rfl⟩
    apply And.intro
    · rcases lem with ⟨K', T', e1, e2, e3⟩;
      simp at e1; subst e1; subst e2; simp [Surface.KindEnv.translate] at e3; apply e3
    · apply And.intro
      · apply Translation.Ty.ValidCtor wfG lemG k2
      · apply And.intro; assumption
        apply h3; apply k4
  · assumption
  · apply h3 _ lk

  -- exists ctors';
--   apply And.intro
--   · simp [Surface.Ty.translate_ctors]

--     unfold Vect.seq;
--     generalize zdef : Vect.seq_lemma (fun n =>
--         (Core.is_valid_ctor_ty (Core.Global.data 0 x ⟦K⟧ Vect.nil :: G') ⟦(ctors n).snd⟧).bind fun __discr =>
--           some ((ctors n).fst, ⟦(ctors n).snd⟧)) = z at *
--     cases z <;> simp at *
--     case inr v => funext; case _ i =>   unfold ctors'; simp
--     case inl v =>
--       rcases v with ⟨j, v⟩
--       have lem := Option.not_isSome_iff_eq_none.1 v
--       replace lem := Option.bind_eq_none'.1 lem ((ctors j).fst , ⟦(ctors j).snd⟧) x
--       replace ctor_trans := ctor_trans j (ctors j).fst (ctors j).snd rfl
--       rcases ctor_trans with ⟨k1, k2, k3, k4⟩
--       have lemG := Translation.Global.empty_data_wkn x K h2
--       have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
--       have k2' := Translation.Ty.ValidCtor wfG lemG k2
--       -- have k2' := Translation.Ty.ValidCtor k2

--       sorry

--   · simp
-- · apply Core.GlobalWf.data
--   · intro i y T e;
--     replace ctor_trans := ctor_trans i (ctors i).fst (ctors i).snd rfl;
--     rcases ctor_trans with ⟨k1, k2, k3, k4⟩
--     simp [ctors'] at e; rcases e with ⟨e1, e2⟩; subst y; subst T
--     have lemG := Translation.Global.empty_data_wkn x K h2
--     have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
--     have lem := Translation.Ty.sound wfG (G := .data x K Vect.nil :: G) ⟨k1,lemG, rfl⟩
--     apply And.intro
--     · rcases lem with ⟨K', T', e1, e2, e3⟩;
--       simp at e1; subst e1; subst e2; simp [Surface.KindEnv.translate] at e3; apply e3
--     · apply And.intro
--       · apply Translation.Ty.ValidCtor wfG lemG k2
--       · apply And.intro; assumption
--         apply h3; apply k4
--   · assumption
--   · apply h3 _ lk


theorem Translation.ListGlobalWf.sound_isSome :
  ⊢s G ->
  G.translate.isSome
:= by
  sorry

theorem Translation.ListGlobalWf.wf_preserved :
  ⊢s G ->
  G.translate = some G' ->
  ⊢ G'
:= by
  intro wf h1; induction wf generalizing G' <;> simp at *
  case nil => sorry
  case cons => sorry

theorem Translation.ListGlobalWf.sound2 {G : Surface.GlobalEnv} :
  ⊢s G ->
  ∃ G', G.translate = some G' ∧
  ⊢ G'
:= by
  intro wf
  have lem := sound_isSome wf
  generalize zdef : G.translate = z at *
  cases z <;> simp at lem; case _ v =>
  exists v; apply And.intro rfl
  apply wf_preserved wf zdef

-- theorem Translation.ListGlobalWf.sound {G : Surface.GlobalEnv} :
--   ⊢s G ->
--   ∃ G', G.translate = some G' ∧
--   ⊢ G' := by
-- intro wf; induction G <;> simp at *
-- apply Core.ListGlobalWf.nil
-- case cons hd tl ih =>
--   cases wf; case _ wftl wfh =>
--   generalize tldef : Surface.GlobalEnv.translate tl = tl' at *;
--   cases tl' <;> simp at *
--   case none => apply ih wftl
--   case some tl' =>
--     apply Exists.intro _


--     -- generalize gdef : Surface.Ty.translate (Core.Global.data hd.2 hd.3.translate Vect.nil :: tl') [] (hd.4 i).snd = g' at *
--     -- simp [Surface.Ty.translate, List.mapM_cons];
--     sorry

import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Core.Typing

import Translation.Ty.Lemmas
import Translation.Term.Lemmas

theorem Translation.Ty.valid_ctor_ty_sound {G : Core.GlobalEnv} :
  Core.is_valid_ctor_ty G T == some x -> Core.ValidCtor x T := by
intro h
fun_induction Core.is_valid_ctor_ty <;> simp at *
case _ ih => replace ih := ih h; apply Core.ValidCtor.all ih
case _ ih => replace ih := ih h; apply Core.ValidCtor.arrow ih
case _ =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨tnf, h1, h2⟩;
  simp at h2; rcases h2 with ⟨h2, e⟩; subst x
  apply Core.ValidCtor.base; apply h1

theorem Translation.Ty.ValidCtor :
  Surface.ValidCtor x T -> Core.ValidCtor x ⟦T⟧ := by
intro h; induction h <;> simp at *
case base h =>
  replace lem := Translation.Ty.Spine h rfl
  rcases lem with ⟨_, lem⟩
  constructor; assumption
case all ih => apply Core.ValidCtor.all ih
case arrow ih => apply Core.ValidCtor.arrow ih

theorem Translation.Ty.valid_ctor_ty_complete {G : Core.GlobalEnv}:
  Core.is_data G x ->
  Core.ValidCtor x T -> Core.is_valid_ctor_ty G T == some x := by
intro h1 h
induction T using Core.is_valid_ctor_ty.induct generalizing G x <;> simp [Core.is_valid_ctor_ty] at *
case _ ih =>
  cases h
  case _ h => simp [Core.Ty.spine] at h
  case _ h => apply ih h1 h
case _ ih =>
  cases h
  case _ h => simp [Core.Ty.spine] at h
  case _ h => apply ih h1 h
case _ =>
  rw[Option.bind_eq_some_iff];
  cases h
  case base sp tnf =>
    exists (x, sp)
    apply And.intro
    apply tnf
    simp; assumption
  case _ h => simp [Core.Ty.spine]; sorry
  case _ => simp [Core.Ty.spine]; sorry

-- induction h <;> simp [Core.is_valid_ctor_ty] at *
-- case all ih => assumption
-- case arrow => assumption
-- case base => sorry

theorem Translation.Global.empty_data_wkn {G : Surface.GlobalEnv} {G' : Core.GlobalEnv} (x : String) (K : Surface.Kind) :
  G.translate = some G' ->
  Surface.GlobalEnv.translate (.data x K Vect.nil :: G) = some (.data 0 x ⟦K⟧ Vect.nil :: G') := by
intro h; simp [Surface.GlobalEnv.translate]
rw[Option.bind_eq_some_iff]; exists G'

theorem Surface.GlobalEnvWf.empty_data_wkn x K : ⊢s G -> lookup x G = none -> ⊢s (Surface.Global.data x K Vect.nil :: G) := by
 intro wf lk; apply ListGlobalWf.cons
 · apply GlobalWf.data <;> try simp at *
   apply Vect.nil
   apply lk
 · assumption


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
let ctors' : Vect n (String × Core.Ty) := (λ x => (x.fst , x.snd.translate)) <$> ctors
exists Core.Global.data n x ⟦K⟧ ctors'
rw[Option.bind_eq_some_iff];
apply And.intro
· exists ctors';
  apply And.intro
  · simp [Surface.Ty.translate_ctors]

    unfold Vect.seq;
    generalize zdef : Vect.seq_lemma (fun n =>
        (Core.is_valid_ctor_ty (Core.Global.data 0 x ⟦K⟧ Vect.nil :: G') ⟦(ctors n).snd⟧).bind fun __discr =>
          some ((ctors n).fst, ⟦(ctors n).snd⟧)) = z at *
    cases z <;> simp at *
    case inr v => funext; case _ i =>   unfold ctors'; simp
    case inl v =>
      rcases v with ⟨j, v⟩
      have lem := Option.not_isSome_iff_eq_none.1 v
      replace lem := Option.bind_eq_none'.1 lem ((ctors j).fst , ⟦(ctors j).snd⟧) x
      replace ctor_trans := ctor_trans j (ctors j).fst (ctors j).snd rfl
      rcases ctor_trans with ⟨k1, k2, k3, k4⟩
      have k2' := Translation.Ty.ValidCtor k2
      sorry

  · simp
· apply Core.GlobalWf.data
  · intro i y T e;
    replace ctor_trans := ctor_trans i (ctors i).fst (ctors i).snd rfl;
    rcases ctor_trans with ⟨k1, k2, k3, k4⟩
    simp [ctors'] at e; rcases e with ⟨e1, e2⟩; subst y; subst T
    apply And.intro
    · have lemG := Translation.Global.empty_data_wkn x K h2
      have wfG := Surface.GlobalEnvWf.empty_data_wkn x K wf lk
      have lem := Translation.Ty.sound wfG (G := .data x K Vect.nil :: G) ⟨k1,lemG, rfl⟩
      rcases lem with ⟨K', T', e1, e2, e3⟩;
      simp at e1; subst e1; subst e2; simp [Surface.KindEnv.translate] at e3; apply e3
    · apply And.intro
      · apply Translation.Ty.ValidCtor k2
      · apply And.intro; assumption;
        apply h3; apply k4
  · assumption
  · apply h3 _ lk


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

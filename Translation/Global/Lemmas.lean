import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Lilac
open Lilac

namespace Translation

theorem Core.Query.opn_strengthen_ctor :
  Core.Query (Core.Global.data n s K ctors :: Γ) Core.DataConst.opn q Ts ->
  Core.Query Γ Core.DataConst.opn q Ts := by sorry

theorem Core.Query.opn_weaken_ctor :
  Core.Query Γ Core.DataConst.opn q Ts ->
  Core.Query (Core.Global.data n s K ctors :: Γ) Core.DataConst.opn q Ts
   := by sorry


theorem Intermediate.Query.opn_weaken_ctor {Γ : Intermediate.GlobalEnv} (wf : ⊢ Γ) :
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts ->
  Intermediate.Query (Intermediate.Global.data n s K ctors :: Γ) Intermediate.DataConst.opn q Ts := by
intro h
induction h generalizing n s K ctors
· constructor
· constructor
  · sorry
  · sorry

theorem Intermediate.Query.opn_weaken {Γ : Intermediate.GlobalEnv} (wf : ⊢ (g::Γ)) :
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts ->
  Intermediate.Query (g :: Γ) Intermediate.DataConst.opn q Ts := by
intro h
induction h generalizing g
· constructor
· constructor
  · sorry
  · sorry


theorem Intermediate.Query.opn_strengthen_ctor {Γ : Intermediate.GlobalEnv} (wf : ⊢ Γ) :
  Intermediate.Query ((Intermediate.Global.data n s K ctors)::Γ) Intermediate.DataConst.opn q Ts ->
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts := by sorry

theorem translate_SI_wf_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  ⊢ G' := by
intro h
fun_induction translate_SI generalizing G' <;> simp at *
case _ =>
  subst h; constructor
case _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h1, h⟩
  simp at h; rcases h with ⟨h2, h⟩
  subst h; cases wf; case _ wftl wfhd =>
  cases wfhd; case _ hd1 hd2 hd3 =>
  constructor
  · constructor
    · intro i y T e
      apply And.intro
      · sorry
      · have lem := hd3 i y T e; rcases lem with ⟨h3, h4⟩; apply And.intro
        · apply h3
        · sorry
    · apply hd2
    · apply h2
  · apply ih wftl h1
sorry
sorry
sorry


theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  Ω G' := by
intro h
have wf' := translate_SI_wf_sound wf h
intro x na nb nc Ks1 Ks2 Ts R q h1 h2
fun_induction translate_SI generalizing G' x <;> simp at *
· subst h; simp [Intermediate.lookup] at h1
case _ ih => -- data
  cases wf; case _ wftl wfhd =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h3, h⟩
  simp at h; rcases h with ⟨h, h2⟩; subst G'
  cases wf'; case _ wftl' wfhd' =>
  simp [Intermediate.lookup] at h1;
  split at h1
  case _ e => subst e; simp at h1
  case _ e =>
    replace h1 := Vec.fold_or h1
    cases h1
    case _ h1 =>
      replace h2 := Intermediate.Query.opn_strengthen_ctor wftl' h2
      replace ih := @ih _ wftl h3 wftl' x h1 h2
      rcases ih with ⟨i, b, p, ih1, ih2⟩
      exists i + 1; exists b; exists p
    case _ h1 => rcases h1 with ⟨i, h1⟩; simp at h1
case _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h3, h⟩
  simp at h
  sorry
case _ ih => sorry
case _ ih => sorry


theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  ⟦ G ⟧ = some G' ->
  Core.Query G' Core.DataConst.opn q Ts ->
  Intermediate.Query G Intermediate.DataConst.opn q Ts := by
intro h1 h2
simp at h1 h2
fun_induction translate_IC generalizing G' <;> simp at *
· subst h1;
  simp [Intermediate.Query, Core.Query, Core.lookup_ctor?] at *
  simp [Intermediate.lookup_ctor?, Core.lookup, Intermediate.lookup] at *
  apply h2
case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'
  replace h2 := Core.Query.opn_strengthen_ctor h2
  cases wf; case _ wftl wfhd =>
  replace ih := ih wftl h3 h2
  apply Intermediate.Query.opn_weaken_ctor wftl ih
sorry
sorry
sorry
sorry
sorry


theorem translate_IC_indexing_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} :
  ⟦ G ⟧ = some G' ->
  G'[i]? = some (Core.Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  G[i]? = some (Intermediate.Global.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩)
   := by
intro h1 h2
fun_induction translate_IC generalizing G' i <;> simp at *
case _ => -- nil
  subst h1; simp at h2
all_goals try (
case _ ih => -- data
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'
  replace ih := ih (i := i - 1) h3
  cases i <;> simp at *
  apply ih h2)
case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h4, h1⟩
  simp at h1; subst G'
  replace ih := ih (i := i - 1) h3
  cases i <;> simp at *
  apply ih h2
case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst h1
  replace ih := ih (i := i - 1) h3
  cases i <;> simp at *
  apply h2
  apply ih h2

case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  split at h1
  · simp at h1
    rcases h1 with ⟨⟨e1, e2⟩, h1⟩;
    subst e1; subst e2
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ps, h4, h1⟩
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ps, h5, h1⟩
    simp at h1; subst G'
    replace ih := ih (i := i - 1) h3
    cases i <;> simp at *
    apply ih h2
  · cases h1


theorem translate_IC_indexing_inst {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} :
  ⟦ G ⟧ = some G' ->
  G[i]? = some (Intermediate.Global.inst x p b) ->
  ∃ b', G'[i]? = some (Core.Global.inst x p b')
   := by
intro h1 h2
simp at h1 h2
fun_induction translate_IC generalizing G' i <;> simp at *
all_goals try (case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
  simp at h3; subst G'
  replace ih := ih (i := i - 1) h1
  cases i <;> simp at *
  apply ih h2)
case _ ih => -- defn
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩;
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h4, h1⟩
  simp at h1; subst G'
  replace ih := ih (i := i - 1) h3
  cases i <;> simp at *
  apply ih h2
case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩;
  split at h1
  · simp at h1;
    rcases h1 with ⟨⟨e1, e2⟩, h1⟩;
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ps', h4, h1⟩
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h5, h1⟩
    simp at h1; subst G'
    replace ih := ih (i := i - 1) h3
    cases i <;> simp at *
    · subst e1; subst e2;
      rcases h2 with ⟨e1, e2, e3, e4⟩; subst e1; subst e2; simp at e3; subst e3; subst e4; simp
    · apply ih h2
  · cases h1


theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  ⟦ G ⟧ = some G' ->
  Core.lookup x G' = some (Core.Entry.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  Intermediate.lookup x G = some (Intermediate.Entry.openm x ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) := by
intro h1 h2
simp at h1 h2
fun_induction translate_IC generalizing G' x <;> simp at *
case _ =>
  subst h1; simp [Core.lookup] at h2
case _ ih =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h2, h1⟩
  simp at h1; subst h1; simp [Core.lookup] at h2
  split at h2
  case _ e =>
    subst e; simp at h2
  case _ e =>
    replace h2 := Vec.fold_or h2
    cases h2
    case _ h3 =>
      replace ih := ih h2 h3;
      simp [Intermediate.lookup]; rw[ite_cond_eq_false]
      · rw[ih]; rw[Vec.fold_or_val_eq]
      · simp; apply e
    case _ h3 => rcases h3 with ⟨i, h3⟩; simp at h3
case _ ih =>  -- defn
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h4, h1⟩
  simp at h1; subst G'; simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false]
    · apply ih h3 h2
    · simp; apply e
all_goals try (case _ ih => -- odata
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'; simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false]
    · apply ih h3 h2
    · simp; apply e)
case _ ih => -- openm
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'; simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2; subst h2; simp [Intermediate.lookup]
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false]
    · apply ih h3 h2
    · simp; apply e
case _ ih => -- inst
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  split at h1;
  · simp at h1
    rcases h1 with ⟨⟨e1, e2⟩, h1⟩
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ps, h4, h1⟩
    rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h5, h1⟩
    simp at h1; subst G'
    subst e1; subst e2;
    simp [Core.lookup] at h2
    simp [Intermediate.lookup]
    apply ih h3 h2
  · cases h1

theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  Ω G ->
  ⟦ G ⟧ = some G' ->
  Ω G' := by
intro oe h1
intro x na nb nc Ks1 Ks2 Ts R q h2 h3
simp at h1 h2 h3
have lem1 := translate_IC_lookup_openm h1 h2
have lem2 := translate_IC_query wf h1 h3
replace oe := @oe x na nb nc Ks1 Ks2 Ts R q lem1 lem2
rcases oe with ⟨i, b, p, oe1, oe2⟩
have lem3 := translate_IC_indexing_inst h1 oe1
rcases lem3 with ⟨b', lem3⟩
exists i; exists b'; exists p

theorem translate_open_exhaustive_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} {G'' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  ⟦ G' ⟧ = some G'' ->
  Ω G'' := by
intro h1 h2
have wf' := translate_SI_wf_sound wf h1
have lem : Ω G' := translate_SI_sound wf h1
have lem2 : Ω G'' := translate_IC_sound wf' lem h2
apply lem2


-- inductive Translation.GlobalWf : Surface.GlobalEnv -> Core.GlobalEnv -> Surface.Global -> Prop where
-- | data {ctors : Vect n (String × Surface.Ty)} {G : Surface.GlobalEnv}{G' : Core.GlobalEnv}:
--   (∀ i y T, ctors i = (y, T) ->
--     (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidCtor x T
--     ∧ x ≠ y
--     ∧ Surface.lookup y G = none) ->
--   (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
--   Surface.lookup x G = none ->
--   GlobalWf G G' (Surface.Global.data x K ctors)
-- | defn :
--   Surface.lookup x G = none ->
--   G&[] ⊢s T : `★ ->
--   Surface.Term.Elab G G' .chk [] [] t T t' ->
--   GlobalWf G G' (Surface.Global.defn x T t)
-- | classDecl :
--   Surface.lookup s G = none ->
--   Surface.ValidOpenKind K ->
--   (∀ i j, (ms i).1 ≠ (ms j).1) ->
--   (∀ i y T, ms i = (y, T) ->
--     (Surface.Global.classDecl s K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidClassMethodTy s T
--     ∧ s ≠ y
--     ∧ Surface.lookup y G = none) ->
--   GlobalWf G G' (Surface.Global.classDecl s K ms)
-- | instDecl :
--   Surface.ValidClassInstTy C T ->
--   -- TODO: Do Non-overlapping check here
--   Surface.lookup C G = some (.opent C K ms') ->
--   -- TODO: check for method types
--   GlobalWf G G' (.instDecl T ms)


-- inductive ValidClassDecl (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (x : String) (K: Surface.Kind) :
--           {n : Nat} -> (Vect n (String × Surface.Ty)) -> Core.GlobalEnv -> Prop where
-- | nil :
--   Surface.lookup x G = none ->
--   Surface.ValidOpenKind K ->
--   ValidClassDecl G G' x K Vect.nil (List.cons (.opent x K.translate) G')
-- | cons {n : Nat} {ms : Vect n (String × Surface.Ty)} {m : String} {τ : Surface.Ty} :
--   ms' = ms.to_list.map (λ (x, τ) => Core.Global.openm x τ.translate) ->
--   ValidClassDecl G G' x K ms (ms' ++ List.cons (.opent x K.translate) G')  ->

--   -- method names are unique
--   Surface.lookup m (.classDecl x K ms :: G) = none ->

--   -- method type is okayg
--   Surface.ValidClassMethodTy x τ ->
--   (.classDecl x K ms :: G)&[] ⊢s τ : `★ ->

--   ValidClassDecl G G' x K (n := n + 1)
--                  (Vect.cons (m , τ) ms)
--                  (List.cons (Core.Global.openm m τ.translate)
--                  (ms' ++ List.cons (.opent x K.translate) G'))


-- inductive ValidInstDecl (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) :
--           Ty -> Vect n (String × Surface.Term) -> Core.GlobalEnv -> Prop where



-- inductive Surface.Global.Elab : Surface.GlobalEnv -> Core.GlobalEnv -> Prop
-- | nil : Surface.Global.Elab [] []

-- | defn :
--   Surface.Global.Elab G G' ->

--   Surface.lookup x G = none ->
--   G&[] ⊢s T : `★ ->
--   Surface.Term.Elab G G' .chk [] [] t T t' ->

--   Surface.Global.Elab (.cons (.defn x T t) G) ((.defn x (T.translate) t') :: G')

-- | data {n : Nat} {ctors : Vect n (String × Ty)} {ctors' : Vect n (String × Core.Ty)} :
--   Surface.Global.Elab G G' ->

--   (∀ i y T, ctors i = (y, T) ->
--     (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
--     ∧ Surface.ValidCtor x T
--     ∧ x ≠ y
--     ∧ Surface.lookup y G = none) ->
--   (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
--   Surface.lookup x G = none ->

--   ctors' = (λ i => ((ctors i).1 , (ctors i).2.translate)) ->

--   Surface.Global.Elab (.cons (.data (n := n) x K ctors) G) (.cons (.data n x K.translate ctors') G')

-- | classDecl {n : Nat} {ms : Vect n (String × Ty)} {Δ : Core.GlobalEnv} :
--   Surface.Global.Elab G G' ->
--   ValidClassDecl G G' x K ms Δ ->
--   Surface.Global.Elab ((.classDecl x K ms) :: G) Δ

-- | instDecl {n} {ms : Vect n (String × Term)} {Δ : Core.GlobalEnv} :
--   Surface.Global.Elab G G' ->
--   ValidInstDecl G G' τ ms Δ ->
--   Surface.Global.Elab G Δ


-- notation:170 G:170 " -↪ " G':170 => Surface.Global.Elab G G'


-- theorem Translation.ValidOpenKind.Sound {K : Surface.Kind}:
--   Surface.ValidOpenKind K -> Core.ValidOpenKind K.translate := by
--   intro h
--   induction h <;> simp at *
--   constructor
--   constructor; assumption

-- theorem Surface.Global.ValidClassDecl.sound :
--   G -↪ G' ->
--   ⊢ G' ->
--   ValidClassDecl G G' x K ms Δ ->
--   ⊢ Δ ∧ Core.Global.Determined Δ := by
-- intro h1 h2 h3
-- induction h3
-- case nil lk vk =>
--   apply And.intro
--   · apply Core.ListGlobalWf.cons _ h2
--     apply Core.GlobalWf.opent (Translation.ValidOpenKind.Sound vk)
--     · apply Translation.GlobalEnv.lookup_none_sound x h1 lk
--   · sorry
-- case cons Δ oms τ ms m T k2 lk k3 k4 k5 ih =>
--   apply And.intro
--   · apply Core.ListGlobalWf.cons
--     apply Core.GlobalWf.openm
--     · sorry
--     · rw[k2]; simp

--       sorry
--     · sorry
--     apply ih.1
--   sorry



-- theorem Surface.Global.Elab.sound :
--   G -↪ G' ->
--   ⊢ G' ∧ Core.Global.Determined G' := by
-- intro h
-- induction h
-- case nil =>
--   apply And.intro
--   · apply Core.ListGlobalWf.nil;
--   · simp [Core.Global.Determined, Core.Determined.openm, Core.Determined.defn, Core.lookup];
-- case defn x T t t' j0 lk j1 j2 ih =>
--   replace j1 := Translation.Ty.sound j1 j0
--   replace j2 := Translation.Term.Sound j0 j2
--   apply And.intro
--   · apply Core.ListGlobalWf.cons _ ih.1
--     apply Core.GlobalWf.defn j1 j2.2
--     apply Translation.GlobalEnv.lookup_none_sound x j0 lk
--   · simp[Core.Global.Determined]; intro x
--     apply And.intro
--     sorry
--     sorry

-- case data G G' x K n ctors ctors' j0 h1 h2 h3 ctors'def ih  =>
--   apply And.intro
--   · apply Core.ListGlobalWf.cons _ ih.1;
--     apply Core.GlobalWf.data
--     · intro i y T h1';
--       simp [ctors'def] at h1'; rcases h1' with ⟨h1a, h1b⟩
--       replace h1 := h1 i (ctors i).fst (ctors i).snd rfl;
--       rcases h1 with ⟨h2a, h2b, h2c, h2d⟩
--       have wkn_j0 : Elab (.data x K Vect.nil :: G) (.cons (.data 0 x K.translate Vect.nil) G') := by
--         apply Elab.data j0; simp; simp; apply h3; simp

--       replace h2a := Translation.Ty.sound h2a wkn_j0
--       subst y; subst T
--       replace h2d := Translation.GlobalEnv.lookup_none_sound (ctors i).fst j0 h2d
--       grind
--     · intro i j; simp [ctors'def]; apply h2
--     · apply Translation.GlobalEnv.lookup_none_sound x j0 h3
--   · sorry
-- case classDecl G G' x K n ms Δ j0 h1 h2 =>
--   apply Surface.Global.ValidClassDecl.sound j0 h2.1 h1
-- case instDecl => sorry

end Translation

import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Lilac
open Lilac

namespace Translation

theorem Except.bind_eq_ok_iff {α : Type u_1} {β : Type u_2} {ε : Type u_3} {b : β} {x : Except ε α} {f : α → Except ε β} :
  x.bind f = .ok b ↔ ∃ (a : α), x = .ok a ∧ f a = .ok b
:= by
  apply Iff.intro
  all_goals (intro h; cases x <;> simp [Except.bind] at *; apply h)

@[simp]
theorem Except.ite_true_eq_ok_iff {α : Type u_1} {t : TM α} {t' : α} {b : Bool} {e : Std.Format}:
  ((if b then t else Except.error e) = Except.ok t') <->
  t = .ok t' ∧ b = True
:= by
  apply Iff.intro
  intro h; split at h <;> simp at h
  case _ b => apply And.intro; apply h; simp; apply b
  intro h; rcases h with ⟨h1, h2⟩; subst h1; simp at h2; subst h2; simp

@[simp]
theorem Except.ite_false_eq_ok_iff {α : Type u_1} {t : TM α} {t' : α} {b : Bool} {e : Std.Format}:
  ((if b then Except.error e else t) = Except.ok t') <->
  t = .ok t' ∧ b = False
:= by
  apply Iff.intro
  intro h; split at h <;> try simp at h
  case _ b => apply And.intro; apply h; simp at b; simp; apply b
  intro h; rcases h with ⟨h1, h2⟩; subst h1; simp at h2; subst h2; simp


-- theorem Core.Query.opn_strengthen_ctor :
--   Core.Query (Core.Global.data n s K ctors :: Γ) Core.DataConst.opn q Ts ->
--   Core.Query Γ Core.DataConst.opn q Ts := by sorry

-- theorem Core.Query.opn_weaken_ctor :
--   Core.Query Γ Core.DataConst.opn q Ts ->
--   Core.Query (Core.Global.data n s K ctors :: Γ) Core.DataConst.opn q Ts
--    := by sorry


-- theorem Intermediate.Query.opn_weaken_ctor {Γ : Intermediate.GlobalEnv} (wf : ⊢ Γ) :
--   Intermediate.Query Γ Intermediate.DataConst.opn q Ts ->
--   Intermediate.Query (Intermediate.Global.data n s K ctors :: Γ) Intermediate.DataConst.opn q Ts := by
-- intro h
-- induction h generalizing n s K ctors
-- · constructor
-- · constructor
--   · sorry
--   · sorry

-- theorem Intermediate.Query.opn_weaken {Γ : Intermediate.GlobalEnv} (wf : ⊢ (g::Γ)) :
--   Intermediate.Query Γ Intermediate.DataConst.opn q Ts ->
--   Intermediate.Query (g :: Γ) Intermediate.DataConst.opn q Ts := by
-- intro h
-- induction h generalizing g
-- · constructor
-- · constructor
--   · sorry
--   · sorry


-- theorem Intermediate.Query.opn_strengthen_ctor {Γ : Intermediate.GlobalEnv} (wf : ⊢ Γ) :
--   Intermediate.Query ((Intermediate.Global.data n s K ctors)::Γ) Intermediate.DataConst.opn q Ts ->
--   Intermediate.Query Γ Intermediate.DataConst.opn q Ts := by sorry
theorem Core.lookup_append_none {G1 G2 : Core.GlobalEnv} :
  Core.lookup x (G1 ++ G2) = none ->
  Core.lookup x G1 = none ∧ Core.lookup x G2 = none
:= by
 intro h1
 induction G1 generalizing G2 <;> simp at *
 sorry
 sorry


theorem translate_IC_lookup_some_octor {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}:
  ⟦ G ⟧ = .ok G' ->
  Core.lookup x G' = Core.Entry.octor y R ->
  Intermediate.lookup x G = Intermediate.Entry.octor y R
:= by
intro h1 h2
fun_induction translate_IC generalizing G' <;> simp at *
case _ => -- nil
  simp [pure, Except.pure] at h1; subst G'; simp [Core.lookup] at h2
case _ ih => sorry
  -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
  -- subst h3; simp [Core.lookup] at h2
  -- split at h2
  -- simp at h2
  -- replace h2 := Vec.fold_or h2; cases h2
  -- case _ h2 =>
  --    simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  --    replace ih := ih h1 h2; rw[ih]
  --    rw[Vec.fold_or_val_eq]
  -- case _ h =>
  --   rcases h with ⟨i, h4⟩; simp at h4
case _ ih => sorry
  -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3, h4, h5⟩; subst G'
  -- simp [Core.lookup] at h2
  -- split at h2
  -- case _ e => subst e; simp at h2
  -- case _ e =>
  --   simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  --   replace ih := ih h1 h2; apply ih
all_goals try (case _ ih =>  sorry
  -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩; subst G'
  -- simp [Core.lookup] at h2
  -- split at h2
  -- case _ e => subst e; simp at h2
  -- case _ e =>
  --   simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  --   replace ih := ih h1 h2; apply ih
)
-- case _ ih =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩; subst G'
--   replace h2 := Core.lookup_append h2
--   cases h2
--   case _ h2 => exfalso; simp at h2; sorry
--   case _ h2 =>
--     rcases h2 with ⟨h2, h3⟩;
--     simp[Intermediate.lookup]
--     split
--     case _ e =>
--       subst e; simp;
--       replace h2 := Core.lookup_append_none h2; rcases h2 with ⟨_, h2⟩
--       simp [Core.lookup] at h2
--     case _ e =>
--       split
--       case _ => sorry
--       case _ =>
--         split
--         · sorry
--         · sorry
  -- simp [Core.lookup] at h2
  -- split at h2
  -- case _ e =>
  --   simp at h2; rcases h2 with ⟨e1, e2⟩; subst e1; subst e2; subst e
  --   simp [Intermediate.lookup]
  -- case _ e =>
  --   simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  --   replace ih := ih h1 h2; apply ih
-- case _ ih =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
--   sorry
  -- split at h3
  -- · simp at h3;
  --   rcases h3 with ⟨⟨e1, e2⟩, h3⟩;
  --   simp [Option.bind_eq_some_iff] at h3; rcases h3 with ⟨_, _, h3, h4, h5, h6⟩;
  --   subst G'; subst e1; subst e2
  --   simp [Core.lookup] at h2
  --   replace ih := ih h1 h2
  --   simp [Intermediate.lookup]; apply ih
  -- · cases h3

-- theorem translate_SI_lookup_none {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}:
--   ⟦ G ⟧ = some G' ->
--   Surface.lookup x G = none ->
--   Intermediate.lookup x G' = none
-- := by sorry


-- theorem translate_IC_lookup_none {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}:
--   ⟦ G ⟧ = some G' ->
--   Core.lookup x G' = none ->
--   Intermediate.lookup x G = none
-- := by
-- intro h1 h2
-- fun_induction translate_IC generalizing G' <;> simp at *
-- case _ =>
--   subst G'; simp [Intermediate.lookup]
-- case _ ih =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
--   subst G'; simp [Core.lookup] at h2; simp [Intermediate.lookup]
--   split at h2
--   · simp at h2
--   · rw[Vec.fold_or_val_eq_none] at h2; rcases h2 with ⟨h2, h3⟩
--     split
--     case _ e1 e2 => exfalso; apply e1 e2
--     rw[Vec.fold_or_val_eq_none]; apply And.intro
--     apply ih h1 h2
--     intro v v1; sorry
-- sorry
-- sorry
-- sorry

theorem mk_inst_mth_SI_sound {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mth_SI Γ' C iname mτs mn tm = .ok i ->
  ∃ n v na nb, i = ⟨mn, 1, #(⟨iname, n, v, na, nb⟩), tm⟩ := by
intro h
unfold mk_inst_mth_SI at h <;> simp at h
split at h
case _ h =>
  split at h <;> try simp [pure, Except.pure, bind, Except.bind_eq_ok_iff] at h;
  rcases h with ⟨s, h1, b, h2, a1, b1, h3⟩;
  split at h3 <;> simp at h3
  subst i;
  case _ e => rcases e with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3; simp
simp at h

theorem mk_inst_mths_SI_sound {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths_SI Γ' C iname ts mτs = .ok insts ->
  ∀ i ∈ insts, ∃ (mn : String) (n na nb : Nat) (v : Vec Core.Ty n) (t : Surface.Term), i = ⟨mn, 1, #(⟨iname, n, v, na, nb⟩), t⟩
:= by
intro h p p_in_insts
fun_induction mk_inst_mths_SI generalizing insts <;> simp [pure, Except.pure] at *
subst h; simp at p_in_insts
case _ mn tm ts ih =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨insts', h, h1⟩
  rcases h1 with ⟨mn, b, h1, h2⟩; subst h2
  simp at p_in_insts; cases p_in_insts
  case _ h =>
    subst h; exists mn; replace h1 := mk_inst_mth_SI_sound h1; rcases h1 with ⟨p, h1⟩; simp at h1; rcases h1 with ⟨e, b⟩
    subst e; rcases b with ⟨n, v, na, nb⟩; subst b; simp
  case _ h2 => apply ih h h2

theorem mk_inst_mths_SI_indexing
{Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths_SI Γ' C iname mτs ts  = .ok insts ->
  (∀ i : Nat, (hi : i < mτs.length) -> ∃ j, ∃ (h : j < insts.length),
    insts[j].1 = mτs[i].1 ∧ insts[j].2.1 = mτs[i].2.2.2.2.2.1)
:= by
 intro h j hj

 sorry

theorem translate_SI_lookup_odata {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup cls G = Surface.Entry.odata cls K mτs ->
  Intermediate.lookup cls G' = Intermediate.Entry.odata cls K' mτs' ->
  K' = mk_cls_kind K ∧ mτs = mτs'
  := by sorry


theorem translate_SI_wf_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  ⊢ G' := by
intro h
fun_induction translate_SI generalizing G' <;> simp [pure, Except.pure] at *
case _ =>
  subst h; constructor
case _ ctors _ ih =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h⟩
  split at h <;> simp at h
  subst G'; case _ h => rcases h with ⟨h2, h⟩; sorry
  -- case _ h =>
  -- simp at h; sorry -- subst h; cases wf; case _ wftl wfhd =>
  -- cases wfhd; case _ hd1 hd2 hd3 =>
  -- constructor
  -- · constructor
  --   · intro i y T e
  --     apply And.intro
  --     · sorry
  --     · have lem := hd3 i y T e; rcases lem with ⟨h4, h5⟩; apply And.intro
  --       · apply h4
  --       · have lem : (y, T) ∈ ctors := by rw[<-e]; apply Vec.getElem_mem
  --         apply h3 y T lem
  --   · apply hd2
  --   · apply h2
  -- · apply ih wftl h1

sorry
sorry
case _ ih => -- instance
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h⟩
  split at h <;> try simp [Except.bind] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  subst G'
  case _ h2 _ _ h3 _ _ _ _ h4 h5 _ mths h6 h7  =>
  rcases h5 with ⟨e1, e2⟩; subst e1
  cases wf; case _ cls_name K mτs _ _ wftl wfhd =>
  cases wfhd; case _ _ _ _ _ _ _ rsp' _ _ _ lks _ q1 e _ =>
  simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1
  rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1;
  rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; subst q1
  rw[rsp'] at h3; simp [Option.toTM] at h3; cases h3
  have lem := translate_SI_lookup_odata wftl h1 lks h4; rcases lem with ⟨e1, e2⟩; subst e1; subst e2
  simp at h4 h6
  constructor
  · apply Intermediate.GlobalWf.inst
    assumption
    apply h4
    apply h7
    · intro i hi;
      have lem := mk_inst_mths_SI_sound h6
      have lem2 := mk_inst_mths_SI_indexing h6 i hi
      rcases lem2 with ⟨j, h, lem2, lem3⟩
      exists j; exists h; apply And.intro
      symm; assumption
      replace lem := lem mths[j] (by simp); simp at lem
      rcases lem with ⟨mn, n, na, nb, v, t, lem⟩; rw[lem]; simp
      rw[lem] at lem3; simp at lem3; symm; assumption
  · apply ih wftl h1


theorem Intermediate.Query.string_ne {Γ : Intermediate.GlobalEnv} :
  Intermediate.lookup x Γ = none ->
  Intermediate.Query Γ v qs Ts ->
  x ∉ qs := by sorry

theorem GlobalWf.drop_wf {Γ : Intermediate.GlobalEnv} (n : Nat): ⊢ Γ -> ⊢ Γ.drop n := by sorry


theorem Intermediate.lookup_openm {G : Intermediate.GlobalEnv} (wf : ⊢ G):
  Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls spTy) ->
  ∃ K mths, Intermediate.lookup cls G = some (.odata cls K mths)
    ∧ ∃ (j : Nat), mths[j]? = .some ⟨mn, spTy⟩
:= by sorry

theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Ω G' := by
intro h
have wf' := translate_SI_wf_sound wf h
intro mn na nb nc Ks1 Ks2 Ts R q _ h1 h2
fun_induction translate_SI generalizing G' mn <;> simp [pure, Except.pure] at *
· subst h; simp [Intermediate.lookup] at h1
case _ ih => -- data
  cases wf; case _ wftl wfhd =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h3, h⟩
  split at h <;> simp at *
  subst G'
  cases wf'; case _ wftl' wfhd' =>
  simp [Intermediate.lookup] at h1;
  split at h1
  case _ e => subst e; simp at h1
  case _ e =>
    replace h1 := Vec.fold_or h1
    cases h1
    case _ h1 =>
      sorry
      -- replace h2 := Intermediate.Query.opn_strengthen_ctor wftl' h2
      -- replace ih := @ih _ wftl h3 wftl' x h1 h2
      -- rcases ih with ⟨i, b, p, ih1, ih2⟩
      -- exists i + 1; exists b; exists p
    case _ h1 => rcases h1 with ⟨i, h1⟩; simp at h1
case _ ih => -- defn decl
  cases wf; case _ wftl wfhd =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h3, h⟩
  replace ih := ih wftl h3
  sorry
case _ ih => -- class Decl
  sorry
case _ cls1 iname _ _ _ _ _ _ _ _ _ ih =>
  cases wf; case _ wftl wfhd =>
  cases wfhd; case _ cls2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q1 q2 q3 =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h3⟩
  split at h3
  · simp [Option.toTM] at h3
    · split at h3 <;> simp [Except.bind] at h3
      repeat (split at h3 <;> try simp at h3)
      subst G';
      cases wf'; case _ wftl' wfhd' =>
      cases wfhd'; case _ rsp _ _ _ _ lks _ _ _ _ rsp' _ _ e _ _ _ _ lki1 e1 _ _ mths_comp _ _ _ _ lki2 _ _ =>
      cases e; rcases e1 with ⟨e1, e2⟩; cases e1
      simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1
      rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1;
      rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; subst q1
      rw[rsp] at rsp'; simp at rsp'; rcases rsp' with ⟨e1, e2⟩; rw[lki1] at lki2; cases lki2
      simp at lki1; simp at *;

      sorry

  · simp at h3

  -- rcases h3 with ⟨⟨e1, e2⟩, ⟨mths_impls, h3, h4, h5⟩⟩
  -- subst G'; subst e1;
  -- case _ cls_name _ _ rsp q0 =>
  -- cases wf'; case _ wftl' wfhd' =>
  -- cases wfhd'; case _ na nb nc Ks1 Ks2 As rsp' _ _ _ _ _ _ _ _ _ _ _ _  mτs m_impls _ q1' q2' q3' =>
  -- have lem := mk_inst_mths_SI_sound h3;
  -- simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1
  -- rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1;
  -- rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; subst q1
  -- rw[rsp] at rsp'; simp at rsp'; rcases rsp' with ⟨e1, e2⟩; subst e1; subst e2
  -- rw[q0] at q1'; cases q1';
  -- cases String.decEq cls cls_name <;> (simp [Intermediate.lookup] at h1; split at h1 <;> try simp at h1)
  -- case isFalse.isFalse =>

  --   sorry

  -- case isTrue.isFalse e _ =>
  -- exists 0; simp; exists iname; exists cls_name; exists na; exists nb; exists nc; simp;
  -- exists Ks1; exists Ks2; exists As; exists []; exists []; exists mths_impls; simp;
  -- have lem := Intermediate.lookup_openm wftl' h1
  -- rcases lem with ⟨K, mths, lem1, lem2⟩
  -- subst e; rw[lem1] at q1'; cases q1'; rw[q0] at lem1; cases lem1
  -- rcases lem2 with ⟨j, lem2⟩
  -- simp [List.getElem?_eq_some_iff] at lem2
  -- rcases lem2 with ⟨hj, lem3⟩;
  -- replace q3' := q3' j hj; rcases q3' with ⟨hk, q3'⟩
  -- rw[lem3] at q3'; simp at q3'
  -- rcases q3' with ⟨q3', q4', q5'⟩; subst q4'; subst q5'
  -- simp

  -- -- exists k; exists mths_impls[k].2.2.2; exists mths_impls[k].2.2.1;
  -- -- apply And.intro
  -- -- rw[List.getElem?_eq_some_iff]; exists hk



theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  ⟦ G ⟧ = Except.ok G' ->
  Core.Query G' Core.DataConst.opn q Ts ->
  Intermediate.Query G Intermediate.DataConst.opn q Ts := by
intro h1 h2
simp at h1 h2
induction h2
case nil  => constructor
case cons h _ ih =>
  constructor
  simp [Core.lookup_ctor?] at h;
  split at h;
  · simp [Option.getD_eq_iff] at h;
    rcases h with ⟨ent, lk, h⟩
    cases ent <;> simp [Core.Entry.ctor?] at h
    split at h;
    simp at h; subst h; case _ oc R _ _ _ e1 e2 =>
      simp [Intermediate.lookup_ctor?]; rw[e2]; simp; simp [Option.getD_eq_iff];
      exists Intermediate.Entry.octor oc R
      apply And.intro
      case _ => apply translate_IC_lookup_some_octor h1 lk
      simp [Intermediate.Entry.ctor?, e1]
    cases h
  · cases h
  apply ih


theorem mk_inst_mth_IC_shape :
  mk_inst_mth_IC Γ' mn m p t = Except.ok i ->
  ∃ b, i = .inst mn p b := by
intro h
unfold mk_inst_mth_IC at h
split at h <;> simp at *

-- rcases h with ⟨⟨e1, e2⟩, h⟩; subst e1; subst e2
-- simp [Option.bind_eq_some_iff] at h; rcases h with ⟨ps, b, h1, t', h2, h3⟩
-- subst i; simp
sorry

theorem mk_inst_mths_IC_lookup :
  mk_inst_mths_IC Γ' ms = Except.ok mths' ->
  ¬ Core.lookup mn mths' = some (.openm mn spTy)
  := by
 intro h1 h2
 fun_induction mk_inst_mths_IC generalizing mths' <;> simp at *

 simp [pure, Except.pure] at h1; subst h1; simp [Core.lookup] at h2
 case _ ih =>
 simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨ms', h3, i⟩;
 simp [Functor.map, Except.map] at i
 split at i <;> simp at *
 subst mths'
 case _ h4 =>
 replace h4 := mk_inst_mth_IC_shape h4; rcases h4 with ⟨b', h4⟩
 subst h4; simp [Core.lookup] at h2; apply ih h3 h2

theorem mk_inst_mths_indexing {j : Nat} :
  mk_inst_mths_IC Γ ms = Except.ok mths' ->
  ms[j]? = .some ⟨x, nc, p, b⟩ ->
  ∃ b', mths'[j]? = .some (Core.Global.inst (m := nc) x p b')
:= by
 intro h1 h2
 fun_induction mk_inst_mths_IC generalizing mths' j <;> simp at *
 case _ ih =>
   simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨ms', h1, i⟩
   simp [Functor.map, Except.map] at i
   split at i <;> simp at *
   subst mths'
   cases j <;> simp at *
   case zero h4 =>
     rcases h2 with ⟨e, h2, h3⟩; subst e; subst h2; simp at h3; rcases h3 with ⟨e1, e2⟩;
     subst e1; subst e2; apply mk_inst_mth_IC_shape h4
   case succ n =>
   apply ih h1 h2

theorem translate_IC_indexing_inst_mths {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  G[i]? = some (Intermediate.Global.instDecl ⟨n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩) ->
  (∃ (j1 : Nat), ∃ b p, mths[j1]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p) ->
  ∃ (i2 : Nat), ∃ b p, G'[i2]? = some (Core.Global.inst x p b) ∧ Core.Query.Match q p
:= by
  intro h1 h2 h3
  fun_induction translate_IC generalizing G' i <;> simp at *
  case _ ih =>
    simp [Functor.map, Except.map] at h1; split at h1 <;> simp at h1
    case _ h1 =>
    subst G'
    rcases h3 with ⟨j1, b, p, h3, h4⟩
    cases i <;> simp at h2
    case _ i =>
    cases wf; case _ wftl _ =>
    replace ih := ih (i := i) wftl h1 h2
    rcases ih with ⟨j, b, p, h1, h2⟩
    exists j + 1; exists b; exists p
  case _ ih => -- defn
    sorry
    -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, ⟨e1, e2, e3⟩⟩
    -- subst G'
    -- cases i <;> simp at h2
    -- case _ i =>
    -- cases wf; case _ wftl _ =>
    -- replace ih := ih (i := i) wftl h1 h2
    -- rcases ih with ⟨j, b, p, h1, h2⟩
    -- exists j + 1; exists b; exists p
  case _ s K fds scs mths _ ih => -- class
    -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, e⟩
    -- subst G'
    -- cases i <;> simp at h2
    -- case _ i =>
    -- cases wf; case _ wftl _ =>
    -- replace ih := ih (i := i) wftl h1 h2
    -- rcases ih with ⟨j, b, p, h1, h2⟩
    -- exists mths.length + 1 + j;
    -- exists b; exists p;

    sorry
  case _ iname cls_name k1 k2 k3 Ks1 Ks2 tys _ _ _ _ ih => -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h2⟩
    simp [Functor.map, Except.map] at h2
    split at h2 <;> simp at *
    subst G'
    cases wf; case _ mths_comp wftl wfhd =>
    cases wfhd
    rcases h3 with ⟨j1, b, p, h3, h4⟩
    -- replace h4 := mk_inst_mths_indexing mths_comp h3
    sorry
    -- generalize odef : [Core.Global.octor iname ⟨k1, (Ks1, ⟨k2, (Ks2, ⟨k3, (tys, (gt#cls_name).mkApps_nats (List.range k1).reverse)⟩)⟩)⟩] = octor at *
    -- simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, e⟩;
    -- rcases e with ⟨mths', h4, h5⟩; subst G'
    -- cases i <;> simp at *
    -- · rcases h2 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
    --   subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; subst e7; subst e8; subst e9;
    --   subst e10; subst e11
    --   rcases h3 with ⟨j1, b, p, h6, h7⟩
    --   cases wf; case _ wfhd =>
    --   cases wfhd; exists j1;
    --   replace h4 := mk_inst_mths_indexing h4 h6
    --   rcases h4 with ⟨b', h4⟩
    --   exists b'; exists p;
    --   apply And.intro
    --   have lem := List.getElem?_append_left (l₁ := mths') (l₂ := octor ++ Γ') (i := j1) (hn := by grind)
    --   grind
    --   apply h7
    -- · case _ i =>
    --   cases wf; case _ wftl _ =>
    --   replace ih := ih wftl h1 h2
    --   rcases ih with ⟨j1, b, p, ih1, ih2⟩
    --   exists mths'.length + 1 + j1; exists b; exists p;
    --   apply And.intro
    --   · conv =>
    --     lhs
    --     apply List.getElem?_append_right (l₁ := mths' ++ octor) (l₂ := Γ') (i := (mths'.length + 1) + j1) (by grind)
    --     grind
    --   · apply ih2



theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  ∃ cls, Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) := by
intro h1 h2
simp at h1 h2
fun_induction translate_IC generalizing G' mn <;> simp at *
case _ =>
  simp [pure, Except.pure] at h1; subst h1; simp [Core.lookup] at h2
case _ ih =>
  cases wf; case _ wf _ =>
  sorry
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h2, h1⟩
  -- simp at h1; subst h1; simp [Core.lookup] at h2
  -- split at h2
  -- case _ e =>
  --   subst e; simp at h2
  -- case _ e =>
  --   replace h2 := Vec.fold_or h2
  --   cases h2
  --   case _ h3 =>
  --     replace ih := ih wf h2 h3;
  --     simp [Intermediate.lookup]; rw[ite_cond_eq_false]
  --     · rcases ih with ⟨cls, ih⟩; exists cls; rw[ih]; rw[Vec.fold_or_val_eq]
  --     · simp; apply e
  --   case _ h3 => rcases h3 with ⟨i, h3⟩; simp at h3
case _ ih =>  -- defn
  cases wf; case _ wf _ =>
  sorry
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h4, h1⟩
  -- simp at h1; subst G'; simp [Core.lookup] at h2
  -- split at h2
  -- case _ e => subst e; simp at h2
  -- case _ e =>
  --   simp [Intermediate.lookup]; rw[ite_cond_eq_false]
  --   · apply ih wf h3 h2
  --   · simp; apply e
all_goals try (case _ ih => -- odata
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'; simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false]
    · apply ih h3 h2
    · simp; apply e)
case _ cls_name _ _ _ _ _ ih => -- openm
  -- cases wf; case _ wf wfhd =>
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  -- simp at h1; subst G'
  -- replace h2 := Core.lookup_append h2
  -- cases h2
  -- case _ h2 =>
  --   replace h2 := Core.lookup_append h2
  --   cases h2
  --   case _ h2 =>
  --     simp at h2;
  --     exists cls_name
  --     cases wfhd; simp[Intermediate.lookup];
  --     split;
  --     · exfalso; sorry
  --     · split
  --       · exfalso; sorry
  --       · split
  --         case _ h _ _ _ h' =>
  --           simp; rw[List.findIdx?_eq_some_iff_getElem] at h;
  --           simp at h; rcases h with ⟨h1, h2, h3⟩
  --           rw[List.getElem?_eq_getElem h1] at h'; simp at h'
  --           subst mn; rw[h']; simp;
  --           sorry
  --         case _ h _ h' =>
  --           exfalso
  --           rw[List.findIdx?_eq_some_iff_getElem] at h;
  --           simp at h; rcases h with ⟨h1, h2, h3⟩
  --           rw[List.getElem?_eq_getElem h1] at h'; simp at h'
  --   case _ h2 => simp [Core.lookup] at h2
  -- case _ h2 =>
  --   rcases h2 with ⟨_, h2⟩
  --   replace ih := ih wf h3 h2
  --   rcases ih with ⟨cls, ih⟩
  --   exists cls;
    sorry
case _ cls_name _ _ _ _ _ _ _ _ _ _ ih => -- inst
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  -- rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨mths', h4, h1⟩
  -- simp at h1; subst G'
  -- cases wf; case _ wftl wfhd =>
  -- replace ih := @ih mn _ wftl h3
  -- replace h2 := Core.lookup_append h2
  -- cases h2
  -- case _ h2 =>
  --   cases wfhd;
  --   exfalso
  --   replace h2 := Core.lookup_append h2
  --   cases h2
  --   case _ h2 => apply mk_inst_mths_IC_lookup h4 h2
  --   case _ h2 => rcases h2 with ⟨e, h2⟩; simp [Core.lookup] at h2
  -- case _ h2 =>
  --   rcases h2 with ⟨h2, h5⟩
  --   replace ih := ih h5; rcases ih with ⟨cls, ih⟩
  --   exists cls; simp [Intermediate.lookup];
  --   split
  --   case _ e =>
  --     exfalso; subst e; cases wfhd; case _ lk _ _ _ => rw[lk] at ih; simp at ih
  --   apply ih
  sorry

-- theorem translate_IC_lookup_openm2 {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
--   ⟦ G ⟧ = .ok G' ->
--   Core.lookup mn G' = some (Core.Entry.openm mn spTy) ->
--   ∃ cls K mths, Intermediate.lookup cls G = some (.odata cls K mths)
--     ∧ ∃ (j : Nat), mths[j]? = .some ⟨mn, spTy⟩
-- := by
-- intro h1 h2
-- fun_induction translate_IC generalizing G' <;> simp at *
-- case _ => simp [pure, Except.pure] at h1; subst h1; simp [Core.lookup] at h2
-- case _ ih =>
--   cases wf; case _ wftl wfhd =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
--   subst G'
--   simp [Core.lookup] at h2
--   split at h2
--   case _ e => subst e; simp at h2
--   replace h2 := Vec.fold_or h2; cases h2;
--   case _ h2 =>
--     replace ih := ih wftl h1 h2
--     rcases ih with ⟨cls, K, mths, ih1, ih2⟩
--     exists cls; exists K; exists mths
--     apply And.intro
--     simp [Intermediate.lookup];
--     split
--     case _ e =>
--       subst e; simp;
--       cases wfhd; case _ lk1 _ _ => exfalso; rw[ih1] at lk1; simp at lk1
--     simp [ih1, Vec.fold_or_val_eq]
--     apply ih2
--   case _ h2 => simp at h2
-- case _ ih =>
--   cases wf; case _ wftl wfhd =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, ⟨t', h3, h4⟩⟩; subst G'
--   cases wfhd; case _ lk _ =>
--   rw[Core.lookup] at h2; simp at h2;
--   split at h2 <;> try simp at h2
--   replace ih := ih wftl h1 h2
--   rcases ih with ⟨cls, K, mths, ih1, ih2⟩
--   exists cls; exists K; exists mths
--   apply And.intro
--   simp [Intermediate.lookup];
--   split
--   case _ e => exfalso; subst e; rw[ih1] at lk; simp at lk
--   apply ih1
--   apply ih2
-- case _ ih =>
--   cases wf; case _ wftl wfhd =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
--   cases wfhd
--   sorry
-- case _ iname cls_name _ _ _ _ _ _ _ _ _ _ ih =>
--   cases wf; case _ wftl wfhd =>
--   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, mth_impls, h3, h4⟩
--   subst G'
--   cases wfhd; case _ lk1 lk2 _ _ =>
--   replace h2 := Core.lookup_append h2
--   cases h2
--   case _ h2 =>
--     replace h2 := Core.lookup_append h2
--     simp at h2; cases h2;
--     simp [Intermediate.lookup]
--     -- contradiction as mth_impls are all insts
--     exfalso; apply mk_inst_mths_IC_lookup h3; assumption
--     case _ h2 => rcases h2 with ⟨_, e⟩; simp [Core.lookup] at e
--   case _ h2 =>
--     rcases h2 with ⟨_, h2⟩
--     replace ih := ih wftl h1 h2; rcases ih with ⟨cls, K, mths, ih⟩
--     exists cls; exists K; exists mths
--     simp [Intermediate.lookup];
--     split
--     case _ e => simp; subst e; rw[lk1] at ih; simp at ih
--     case _ => apply ih


theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  Ω G ->
  ⟦ G ⟧ = .ok G' ->
  Ω G' := by
intro oe h1
intro x na nb nc Ks1 Ks2 Ts R q h2 h3
have lem1 := translate_IC_lookup_openm wf h1 h2
have lem2 := translate_IC_query h1 h3
rcases lem1 with ⟨cls, lem1⟩
replace oe := @oe x na nb nc Ks1 Ks2 Ts R q cls lem1 lem2
rcases oe with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, oe1, j, oe2⟩
cases oe2
case _ oe2 => sorry
case _ oe2 =>
  cases oe2
  case _ oe2 => sorry
  case _ oe2 =>
   have lem := translate_IC_indexing_inst_mths (i := i) wf h1 oe1 oe2
   apply lem



--
-- rcases oe with ⟨i, n, cls_name, k1, k2, k3, Ks1', Ks2', tys, fds, scs, mths, h4, j, oe⟩
-- cases oe
-- case _ oe =>
--   fun_induction translate_IC generalizing G' i <;> simp at *
--   case _ ih =>
--     rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h5, h1⟩
--     simp at h1; subst G'
--     cases wf; case _  wftl wfhd =>
--     replace ih := @ih Γ' wftl h5 sorry sorry sorry sorry i sorry
--     rcases ih with ⟨i, b, p, ih⟩
--     exists i + 1; exists b; exists p
--   case _ ih => sorry
--   case _ ih => sorry
--   case _ ih => sorry
-- case _ oe =>
--   cases oe
--   case _ oe => sorry
--   case _ oe => sorry
-- fun_induction translate_IC generalizing G' <;> simp at *
-- case _ => -- nil
--   sorry
-- case _ ih => -- data
--   rw[Option.bind_eq_some_iff] at h1
--   rcases h1 with ⟨Γ', h4, h1⟩
--   simp at h1; subst G'
--   unfold Intermediate.OpenExhaustive at oe;
--   replace oe := @oe x na nb nc Ks1 Ks2 Ts R q
--   sorry
-- case _ ih => -- defn
--   sorry
-- case _ ih => sorry
-- case _ ih => sorry
-- simp at h1 h2 h3
-- have lem1 := translate_IC_lookup_openm h1 h2
-- have lem2 := translate_IC_query wf h1 h3
-- replace oe := @oe x na nb nc Ks1 Ks2 Ts R q lem1 lem2
-- rcases oe with ⟨i, b, p, oe1, oe2⟩
-- have lem3 := translate_IC_indexing_inst h1 oe1
-- rcases lem3 with ⟨b', lem3⟩
-- exists i; exists b'; exists p

theorem translate_open_exhaustive_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} {G'' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  ⟦ G' ⟧ = .ok G'' ->
  Ω G'' := by
intro h1 h2
have lem : Ω G' := translate_SI_sound wf h1
have wf' : ⊢ G' := translate_SI_wf_sound wf h1
have lem2 : Ω G'' := translate_IC_sound wf' lem h2
apply lem2

end Translation

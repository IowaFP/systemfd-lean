import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Lilac
open Lilac

namespace Translation

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

theorem translate_IC_lookup_some_octor {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}:
  ⟦ G ⟧ = some G' ->
  Core.lookup x G' = Core.Entry.octor y R ->
  Intermediate.lookup x G = Intermediate.Entry.octor y R
:= by
intro h1 h2
fun_induction translate_IC generalizing G' <;> simp at *
case _ => -- nil
  subst G'; simp [Core.lookup] at h2
case _ ih =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
  subst h3; simp [Core.lookup] at h2
  split at h2
  simp at h2
  replace h2 := Vec.fold_or h2; cases h2
  case _ h2 =>
     simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
     replace ih := ih h1 h2; rw[ih]
     rw[Vec.fold_or_val_eq]
  case _ h =>
    rcases h with ⟨i, h4⟩; simp at h4
case _ ih =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3, h4, h5⟩; subst G'
  simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
    replace ih := ih h1 h2; apply ih
all_goals try (case _ ih =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩; subst G'
  simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
    replace ih := ih h1 h2; apply ih)
case _ ih =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩; subst G'
  sorry
  -- simp [Core.lookup] at h2
  -- split at h2
  -- case _ e =>
  --   simp at h2; rcases h2 with ⟨e1, e2⟩; subst e1; subst e2; subst e
  --   simp [Intermediate.lookup]
  -- case _ e =>
  --   simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  --   replace ih := ih h1 h2; apply ih
case _ ih =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
  sorry
  -- split at h3
  -- · simp at h3;
  --   rcases h3 with ⟨⟨e1, e2⟩, h3⟩;
  --   simp [Option.bind_eq_some_iff] at h3; rcases h3 with ⟨_, _, h3, h4, h5, h6⟩;
  --   subst G'; subst e1; subst e2
  --   simp [Core.lookup] at h2
  --   replace ih := ih h1 h2
  --   simp [Intermediate.lookup]; apply ih
  -- · cases h3

theorem translate_SI_lookup_none {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}:
  ⟦ G ⟧ = some G' ->
  Surface.lookup x G = none ->
  Intermediate.lookup x G' = none
:= by sorry


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




theorem translate_SI_wf_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  ⊢ G' := by
intro h
fun_induction translate_SI generalizing G' <;> simp at *
case _ =>
  subst h; constructor
case _ ctors _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h1, h⟩
  simp at h; rcases h with ⟨⟨h2, h3⟩, h⟩
  subst h; cases wf; case _ wftl wfhd =>
  cases wfhd; case _ hd1 hd2 hd3 =>
  constructor
  · constructor
    · intro i y T e
      apply And.intro
      · sorry
      · have lem := hd3 i y T e; rcases lem with ⟨h4, h5⟩; apply And.intro
        · apply h4
        · have lem : (y, T) ∈ ctors := by rw[<-e]; apply Vec.getElem_mem
          apply h3 y T lem
    · apply hd2
    · apply h2
  · apply ih wftl h1
sorry
sorry
case _ ih => -- instance
  simp [Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h1, h⟩
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp [Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨e1, e2⟩, mths, h2, h3, h4⟩
  subst G'; subst e1;
  cases wf; case _ lk wftl wfhd =>
  constructor
  · apply Intermediate.GlobalWf.inst
    assumption
    apply lk
    apply h3
    intro i hi; sorry -- should come from mk_inst_mths_sound
  · apply ih wftl h1



theorem mk_inst_mths_sound {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths Γ' C iname ts mτs = some insts ->
  ∀ i ∈ insts, ∃ (mn : String) (n na nb : Nat) (v : Vec Core.Ty n) (t : Surface.Term), i = ⟨mn, 1, #(⟨iname, n, v, na, nb⟩), t⟩
:= by
intro h p p_in_insts
fun_induction mk_inst_mths generalizing insts <;> simp at *
subst h; simp at p_in_insts
case _ mn tm ts ih =>
  simp [Option.bind_eq_some_iff] at h; rcases h with ⟨insts', h, h1⟩
  split at h1 <;> try simp at h1
  subst insts
  simp at p_in_insts
  cases p_in_insts
  case _ p => subst p; simp
  case _ p_in_insts' => apply ih h p_in_insts'

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
  ⟦ G ⟧ = some G' ->
  Ω G' := by
intro h
have wf' := translate_SI_wf_sound wf h
intro mn na nb nc Ks1 Ks2 Ts R q _ h1 h2
fun_induction translate_SI generalizing G' mn <;> simp at *
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
      sorry
      -- replace h2 := Intermediate.Query.opn_strengthen_ctor wftl' h2
      -- replace ih := @ih _ wftl h3 wftl' x h1 h2
      -- rcases ih with ⟨i, b, p, ih1, ih2⟩
      -- exists i + 1; exists b; exists p
    case _ h1 => rcases h1 with ⟨i, h1⟩; simp at h1
case _ ih => -- defn decl
  cases wf; case _ wftl wfhd =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h3, h⟩
  simp at h
  replace ih := ih wftl h3
  sorry
case _ ih => -- class Decl
  sorry
case _ cls iname _ _ _ _ _ _ _ _ _ ih =>
  cases wf; case _ wftl wfhd =>
  cases wfhd; case _ q1 q2 q3 =>
  simp [Option.bind_eq_some_iff] at h; rcases h with ⟨Γ', h, h3⟩
  split at h3 <;> try simp at h3
  split at h3 <;> try simp at h3
  split at h3 <;> try simp [Option.bind_eq_some_iff] at h3
  rcases h3 with ⟨⟨e1, e2⟩, ⟨mths_impls, h3, h4, h5⟩⟩
  subst G'; subst e1;
  case _ cls_name _ _ _ _ =>
  cases wf'; case _ wftl' wfhd' =>
  cases wfhd'; case _ na Ks1 nb Ks2 nc As R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q1' q2' q3' =>
  have lem := mk_inst_mths_sound h3;
  cases String.decEq cls cls_name <;> (simp [Intermediate.lookup] at h1; split at h1 <;> try simp at h1)
  case isFalse.isFalse =>

    sorry

  case isTrue.isFalse =>
  exists 0; simp; exists iname; exists cls_name; exists na; exists nb; exists nc; simp;
  exists Ks1; exists Ks2; exists As; exists []; exists []; exists mths_impls; simp;
  have lem := Intermediate.lookup_openm wftl' h1
  rcases lem with ⟨K, mths, lem1, lem2⟩
  sorry


theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  ⟦ G ⟧ = some G' ->
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
  mk_inst_mth_IC Γ' mn m p t = some i ->
  ∃ b, i = .inst mn p b := by
intro h
unfold mk_inst_mth_IC at h
split at h <;> simp at *
rcases h with ⟨⟨e1, e2⟩, h⟩; subst e1; subst e2
simp [Option.bind_eq_some_iff] at h; rcases h with ⟨ps, b, h1, t', h2, h3⟩
subst i; simp


theorem mk_inst_mths_IC_lookup :
  mk_inst_mths_IC Γ' ms = some mths' ->
  ¬ Core.lookup mn mths' = some (.openm mn spTy)
  := by
 intro h1 h2
 fun_induction mk_inst_mths_IC generalizing mths' <;> simp at *
 subst h1; simp [Core.lookup] at h2
 case _ ih =>
 simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ms', h3, i, h4, h5⟩; subst mths'
 replace h4 := mk_inst_mth_IC_shape h4; rcases h4 with ⟨b', h4⟩
 subst h4; simp [Core.lookup] at h2; apply ih h3 h2

theorem mk_inst_mths_indexing {j : Nat} :
  mk_inst_mths_IC Γ ms = some mths' ->
  ms[j]? = .some ⟨x, nc, p, b⟩ ->
  ∃ b', mths'[j]? = .some (Core.Global.inst (m := nc) x p b')
:= by
 intro h1 h2
 fun_induction mk_inst_mths_IC generalizing mths' j <;> simp at *
 case _ ih =>
   simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨ms', h1, inst, h4, h5⟩
   subst h5;
   cases j <;> simp at *
   case zero =>
     rcases h2 with ⟨e, h2, h3⟩; subst e; subst h2; simp at h3; rcases h3 with ⟨e1, e2⟩;
     subst e1; subst e2; apply mk_inst_mth_IC_shape h4
   case succ n =>
   apply ih h1 h2

theorem translate_IC_indexing_inst_mths {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  G[i]? = some (Intermediate.Global.instDecl ⟨n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩) ->
  (∃ (j1 : Nat), ∃ b p, mths[j1]? = some ⟨x, nc, p, b⟩ ∧ Core.Query.Match q p) ->
  ∃ (i2 : Nat), ∃ b p, G'[i2]? = some (Core.Global.inst x p b) ∧ Core.Query.Match q p
:= by
  intro h1 h2 h3
  fun_induction translate_IC generalizing G' i <;> simp at *
  case _ ih =>
    simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, e⟩; subst G'
    rcases h3 with ⟨j1, b, p, h3, h4⟩
    cases i <;> simp at h2
    case _ i =>
    cases wf; case _ wftl _ =>
    replace ih := ih (i := i) wftl h1 h2
    rcases ih with ⟨j, b, p, h1, h2⟩
    exists j + 1; exists b; exists p
  case _ ih => -- defn
    simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, ⟨e1, e2, e3⟩⟩
    subst G'
    cases i <;> simp at h2
    case _ i =>
    cases wf; case _ wftl _ =>
    replace ih := ih (i := i) wftl h1 h2
    rcases ih with ⟨j, b, p, h1, h2⟩
    exists j + 1; exists b; exists p
  case _ ih => -- class
    simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, e⟩
    subst G'
    cases i <;> simp at h2
    case _ i =>
    cases wf; case _ wftl _ =>
    replace ih := ih (i := i) wftl h1 h2
    rcases ih with ⟨j, b, p, h1, h2⟩
    exists j + 1;
  case _ iname cls_name k1 k2 k3 Ks1 Ks2 tys _ _ _ _ ih => -- inst
    generalize odef : [Core.Global.octor iname ⟨k1, (Ks1, ⟨k2, (Ks2, ⟨k3, (tys, (gt#cls_name).mkApps_nats (List.range k1).reverse)⟩)⟩)⟩] = octor at *
    simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, e⟩;
    rcases e with ⟨mths', h4, h5⟩; subst G'
    cases i <;> simp at *
    · rcases h2 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
      subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; subst e7; subst e8; subst e9;
      subst e10; subst e11
      rcases h3 with ⟨j1, b, p, h6, h7⟩
      cases wf; case _ wfhd =>
      cases wfhd; exists j1;
      replace h4 := mk_inst_mths_indexing h4 h6
      rcases h4 with ⟨b', h4⟩
      exists b'; exists p;
      apply And.intro
      have lem := List.getElem?_append_left (l₁ := mths') (l₂ := octor ++ Γ') (i := j1) (hn := by grind)
      grind
      apply h7
    · case _ i =>
      cases wf; case _ wftl _ =>
      replace ih := ih wftl h1 h2
      rcases ih with ⟨j1, b, p, ih1, ih2⟩
      exists mths'.length + 1 + j1; exists b; exists p;
      apply And.intro
      · conv =>
        lhs
        apply List.getElem?_append_right (l₁ := mths' ++ octor) (l₂ := Γ') (i := (mths'.length + 1) + j1) (by grind)
        grind
      · apply ih2



theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = some G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  ∃ cls, Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) := by
intro h1 h2
simp at h1 h2
fun_induction translate_IC generalizing G' mn <;> simp at *
case _ =>
  subst h1; simp [Core.lookup] at h2
case _ ih =>
  cases wf; case _ wf _ =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h2, h1⟩
  simp at h1; subst h1; simp [Core.lookup] at h2
  split at h2
  case _ e =>
    subst e; simp at h2
  case _ e =>
    replace h2 := Vec.fold_or h2
    cases h2
    case _ h3 =>
      replace ih := ih wf h2 h3;
      simp [Intermediate.lookup]; rw[ite_cond_eq_false]
      · rcases ih with ⟨cls, ih⟩; exists cls; rw[ih]; rw[Vec.fold_or_val_eq]
      · simp; apply e
    case _ h3 => rcases h3 with ⟨i, h3⟩; simp at h3
case _ ih =>  -- defn
  cases wf; case _ wf _ =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨t', h4, h1⟩
  simp at h1; subst G'; simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  case _ e =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false]
    · apply ih wf h3 h2
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
case _ cls_name _ _ _ _ _ ih => -- openm
  cases wf; case _ wf wfhd =>
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp at h1; subst G'
  replace h2 := Core.lookup_append h2
  cases h2
  case _ h2 =>
    replace h2 := Core.lookup_append h2
    cases h2
    case _ h2 =>
      simp at h2;
      exists cls_name
    case _ h2 => simp [Core.lookup] at h2
  case _ h2 =>
    rcases h2 with ⟨_, h2⟩
    replace ih := ih wf h3 h2
    rcases ih with ⟨cls, ih⟩
    exists cls;
case _ cls_name _ _ _ _ _ _ _ _ _ _ ih => -- inst
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  rw[Option.bind_eq_some_iff] at h1; rcases h1 with ⟨mths', h4, h1⟩
  simp at h1; subst G'
  cases wf; case _ wftl wfhd =>
  replace ih := @ih mn _ wftl h3
  replace h2 := Core.lookup_append h2
  cases h2
  case _ h2 =>
    cases wfhd;
    exfalso
    replace h2 := Core.lookup_append h2
    cases h2
    case _ h2 => apply mk_inst_mths_IC_lookup h4 h2
    case _ h2 => rcases h2 with ⟨e, h2⟩; simp [Core.lookup] at h2
  case _ h2 =>
    rcases h2 with ⟨h2, h5⟩
    replace ih := ih h5; rcases ih with ⟨cls, ih⟩
    exists cls; simp [Intermediate.lookup];
    split
    case _ e =>
      exfalso; subst e; cases wfhd; case _ lk _ _ _ => rw[lk] at ih; simp at ih
    apply ih

theorem translate_IC_lookup_openm2 {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  ⟦ G ⟧ = some G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn spTy) ->
  ∃ cls K mths, Intermediate.lookup cls G = some (.odata cls K mths)
    ∧ ∃ (j : Nat), mths[j]? = .some ⟨mn, spTy⟩
:= by
intro h1 h2
fun_induction translate_IC generalizing G' <;> simp at *
case _ => subst h1; simp [Core.lookup] at h2
case _ ih =>
  cases wf; case _ wftl wfhd =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
  subst G'
  simp [Core.lookup] at h2
  split at h2
  case _ e => subst e; simp at h2
  replace h2 := Vec.fold_or h2; cases h2;
  case _ h2 =>
    replace ih := ih wftl h1 h2
    rcases ih with ⟨cls, K, mths, ih1, ih2⟩
    exists cls; exists K; exists mths
    apply And.intro
    simp [Intermediate.lookup];
    split
    case _ e =>
      subst e; simp;
      cases wfhd; case _ lk1 _ _ => exfalso; rw[ih1] at lk1; simp at lk1
    simp [ih1, Vec.fold_or_val_eq]
    apply ih2
  case _ h2 => simp at h2
case _ ih =>
  cases wf; case _ wftl wfhd =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, ⟨t', h3, h4⟩⟩; subst G'
  cases wfhd; case _ lk _ =>
  rw[Core.lookup] at h2; simp at h2;
  split at h2 <;> try simp at h2
  replace ih := ih wftl h1 h2
  rcases ih with ⟨cls, K, mths, ih1, ih2⟩
  exists cls; exists K; exists mths
  apply And.intro
  simp [Intermediate.lookup];
  split
  case _ e => exfalso; subst e; rw[ih1] at lk; simp at lk
  apply ih1
  apply ih2
case _ ih =>
  cases wf; case _ wftl wfhd =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
  cases wfhd
case _ iname cls_name _ _ _ _ _ _ _ _ _ _ ih =>
  cases wf; case _ wftl wfhd =>
  simp [Option.bind_eq_some_iff] at h1; rcases h1 with ⟨Γ', h1, mth_impls, h3, h4⟩
  subst G'
  cases wfhd; case _ lk1 lk2 _ _ =>
  replace h2 := Core.lookup_append h2
  cases h2
  case _ h2 =>
    replace h2 := Core.lookup_append h2
    simp at h2; cases h2;
    simp [Intermediate.lookup]
    -- contradiction as mth_impls are all insts
    exfalso; apply mk_inst_mths_IC_lookup h3; assumption
    case _ h2 => rcases h2 with ⟨_, e⟩; simp [Core.lookup] at e
  case _ h2 =>
    rcases h2 with ⟨_, h2⟩
    replace ih := ih wftl h1 h2; rcases ih with ⟨cls, K, mths, ih⟩
    exists cls; exists K; exists mths
    simp [Intermediate.lookup];
    split
    case _ e => simp; subst e; rw[lk1] at ih; simp at ih
    case _ => apply ih


theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  Ω G ->
  ⟦ G ⟧ = some G' ->
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
  ⟦ G ⟧ = some G' ->
  ⟦ G' ⟧ = some G'' ->
  Ω G'' := by
intro h1 h2
have lem : Ω G' := translate_SI_sound wf h1
have wf' : ⊢ G' := translate_SI_wf_sound wf h1
have lem2 : Ω G'' := translate_IC_sound wf' lem h2
apply lem2

end Translation

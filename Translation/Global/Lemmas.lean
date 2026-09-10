import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Core.Metatheory.Global
import Translation.Term.Lemmas

import Lilac
open Lilac

namespace Core

theorem lookup_append_none {G1 G2 : List Global} :
  Core.lookup x (G1 ++ G2) = none <->
  (Core.lookup x G1 = none ∧ Core.lookup x G2 = none)
:= by
  apply Iff.intro
  intro h1
  induction G1 generalizing G2 <;> simp [lookup] at *
  apply h1
  case _ hd tl ih =>
    cases hd <;> simp [lookup] at *
    case data s _ _ =>
      split at h1 <;> try simp at h1
      simp [Vec.fold_or_val_eq_none] at h1;
      rcases h1 with ⟨h1, h2⟩
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e), Vec.fold_or_val_eq_none];
      apply And.intro
      grind
      replace ih := ih h1; apply ih.2
    all_goals try (case _ s _ =>
      split at h1 <;> try simp at h1
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e)];
      apply ih h1)
    case _ s _ _ =>
      split at h1 <;> try simp at h1
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e)];
      apply ih h1
    case inst => apply ih h1

  intro h1; rcases h1 with ⟨h1, h2⟩
  induction G1 generalizing G2 <;> simp at *
  apply h2
  case _ hd tl ih =>
    cases hd <;> simp [lookup] at *
    case data s _ _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e), Vec.fold_or_val_eq_none];
        simp [Vec.fold_or_val_eq_none] at h1; rcases h1 with ⟨h1, h3⟩
        apply And.intro
        apply ih h1 h2
        apply h3
    all_goals try (case _ s _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e)]; apply ih h1 h2)
    case defn s _ _ =>
      split at h1 <;> try simp at h1
      case _ e =>
        replace e : (x = s) = False := by grind;
        simp [ite_cond_eq_false (h := e)]; apply ih h1 h2
    case inst => apply ih h1 h2


theorem lookup_append_some {G1 G2 : List Global} {e : Entry} (wf : ⊢ (G1 ++ G2)): -- needs wf in data constructor case
  Core.lookup x (G1 ++ G2) = some e ->
  Core.lookup x G1 = some e ∨ (Core.lookup x G1 = none ∧ Core.lookup x G2 = some e)
:= by
  intro h1
  induction G1 generalizing G2 x
  · apply Or.inr;
    simp [Core.lookup] at *;
    have lem : [] ++ G2 = G2 := by apply List.nil_append
    apply h1
  case _ hd tl ih => -- data
    have leme : hd :: tl ++ G2 = hd :: (tl ++ G2) := by apply List.cons_append
    rw[leme] at h1;
    cases wf; case _ wftl wfhd =>
    cases hd <;> simp [lookup] at h1
    case _ n s k ctors =>
      cases wfhd; case _ c1 c2 c3 =>
      split at h1
      case _ e => subst e; simp at h1; subst e; apply Or.inl; simp [lookup]
      case _ =>
        have lem : (x = s) = False := by grind
        simp [lookup, ite_cond_eq_false (h := lem)]
        replace h1 := Vec.fold_or h1
        cases h1
        case _ h1 =>
          replace ih := ih wftl h1
          cases ih
          case _ e => apply Or.inl; simp [e, Vec.fold_or_val_eq]
          case _ ih =>
            rcases ih with ⟨ih1, ih2⟩; rw[ih1];
            apply Or.inr; apply And.intro; simp [Vec.fold_or_val_eq_none];
            · intro v v_in_vs; clear lem; clear c1; clear c2
              replace v_in_vs := Vec.getElem_of_mem v_in_vs
              rcases v_in_vs with ⟨i, v_in_vs⟩; simp at v_in_vs;
              replace c3 := c3 i ctors[i].fst ctors[i].snd rfl
              split at v_in_vs;
              subst x; simp at *; subst v; rcases c3 with ⟨_, _, c3⟩; exfalso;
              simp [c3] at h1;
              symm; apply v_in_vs
            · apply ih2
        case _ h =>
          rcases h with ⟨i, h⟩; apply Or.inl;
          replace c3 := c3 i ctors[i].1 ctors[i].2 rfl
          rcases c3 with ⟨c3a, c3b, c3c⟩;
          simp at h; rw[<-h.1] at c3c; simp [lookup_append_none] at c3c; rcases c3c with ⟨c3c, c3d⟩
          rw [c3c]; simp [Vec.foldl_or_none_default]; exists i; apply And.intro; apply h
          intro j hi; rw[h.1]; apply c2 i j; grind
    all_goals try (case _ s _ => -- odata, openm
      split at h1;
      case _ e => subst e; simp at h1; subst e; apply Or.inl; simp [lookup]
      case _ =>
        have lem : (x = s) = False := by grind
        simp [lookup, ite_cond_eq_false (h := lem)]
        apply ih wftl h1)
    case _ s _ _ => -- defn, inst
      cases wfhd;
      split at h1;
      case _ e => subst e; simp at h1; subst e; apply Or.inl; simp [lookup]
      case _ =>
        have lem : (x = s) = False := by grind
        simp [lookup, ite_cond_eq_false (h := lem)]
        apply ih wftl h1
    case _ s _ _ => -- inst
        simp [lookup]
        apply ih wftl h1

-- theorem lookup_append_some2 {G1 G2 : List Global} {e : Entry} :
--   Core.lookup x G1 = some e ∨ Core.lookup x G2 = some e ->
--   Core.lookup x (G1 ++ G2) = some e
-- := by
--   intro h1
--   cases h1
--   · induction G2 generalizing G1;
--     simp; assumption
--     sorry
--   sorry
--   intro h1
--   induction G1 generalizing G2 <;> simp [Core.lookup] at *
--   apply h1
--   case _ hd tl ih =>
--     cases hd <;> simp [Core.lookup] at *
--     case data s _ ctors =>
--       split at h1
--       cases h1; subst x; simp
--       case _ e =>
--         replace e : (x = s) = False := by grind
--         simp [ite_cond_eq_false (h := e)];
--         replace h1 := Vec.fold_or h1;
--         cases h1
--         case _ h1 =>
--           replace ih := ih h1
--           cases ih
--           case _ ih => simp [ih, Vec.foldl_or_some_default]
--           apply Or.inr; assumption
--         case _ ent _ _ h1 =>
--           rcases h1 with ⟨i, h1⟩
--           simp at h1; rcases h1 with ⟨e1, e2⟩
--           apply Or.inl;
--           sorry
--     case inst =>
--       apply ih h1
--     case odata s _ =>
--       split at h1
--       subst x; simp; simp at h1; subst e; simp
--       case _ e =>
--         replace e : (x = s) = False := by grind
--         simp [ite_cond_eq_false (h := e)]; apply ih h1
--     case openm s _ =>
--       split at h1
--       subst x; simp; simp at h1; subst e; simp
--       case _ e =>
--         replace e : (x = s) = False := by grind
--         simp [ite_cond_eq_false (h := e)]; apply ih h1
--     case defn s _ _ =>
--       split at h1
--       subst x; simp; simp at h1; subst e; simp
--       case _ e =>
--         replace e : (x = s) = False := by grind
--         simp [ite_cond_eq_false (h := e)]; apply ih h1
--     case octor s _ =>
--       split at h1
--       subst x; simp; simp at h1; subst e; simp
--       case _ e =>
--         replace e : (x = s) = False := by grind
--         simp [ite_cond_eq_false (h := e)]; apply ih h1

end Core

namespace Translation


theorem Except.bind_eq_ok_iff {α : Type u_1} {β : Type u_2} {ε : Type u_3} {b : β} {x : Except ε α} {f : α → Except ε β} :
  x.bind f = .ok b ↔ ∃ (a : α), x = .ok a ∧ f a = .ok b
:= by
  apply Iff.intro
  all_goals (intro h; cases x <;> simp [Except.bind] at *; apply h)

theorem Except.map_eq_ok_iff {α : Type u_1} {β : Type u_2} {ε : Type u_3} {b : β} {x : Except ε α}  {f : α → β} :
  x.map f = .ok b ↔ ∃ (a : α), x = .ok a ∧ f a = b := by
  apply Iff.intro
  intro h; simp [Except.map] at *; split at h <;> (try simp at *); apply h
  intro h; simp [Except.map]; split <;>  (try simp at *); apply h

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

theorem Option.toTM_some_eq_ok_iff :
  Option.toTM s c = Except.ok e <-> c = some e
:= by
  apply Iff.intro;
  intro h; simp [Option.toTM] at h; split at h <;> simp at *
  cases h; rfl
  intro h; subst h; simp [Option.toTM, Except.pure]

theorem Intermediate.Query.opn_strengthen_ctor {Γ : Intermediate.GlobalEnv}
  (wf : ⊢ (Intermediate.Global.data ⟨s, K, ⟨n, ctors⟩⟩ :: Γ)) :
  Intermediate.Query ((Intermediate.Global.data ⟨s, K, ⟨n, ctors⟩⟩ :: Γ)) Core.DataConst.opn q Ts ->
  Intermediate.Query Γ Core.DataConst.opn q Ts
:= by
  intro h
  induction h
  case _ => apply VecTyping.nil
  case _ h1 h2 ih =>
    apply VecTyping.cons
    simp [Intermediate.lookup_ctor?] at h1;
    split at h1 <;> try simp at h1;
    case _ bsp =>
      simp [Intermediate.lookup_ctor?]; simp [bsp];
      simp[Option.getD_eq_iff] at h1; rcases h1 with ⟨ent, lk, h1⟩; simp [Intermediate.lookup] at lk;
      cases wf; case _ wftl wfhd =>
      cases wfhd
      split at lk
      case _ e => subst e; cases lk; case _ lk _ => exfalso; simp [Intermediate.Entry.ctor?] at h1
      replace lk := Vec.fold_or lk;
      cases lk
      case _ e => simp [e]; apply h1
      case _ lk =>
        exfalso
        rcases lk with ⟨i, lk⟩
        cases ent <;> simp at *
        simp [Intermediate.Entry.ctor?] at h1
    apply ih


theorem Intermediate.Query.opn_strengthen_defn {Γ : Intermediate.GlobalEnv}
  (wf : ⊢ (Intermediate.Global.defn ⟨s, T, t⟩ :: Γ)) :
  Intermediate.Query ((Intermediate.Global.defn ⟨s, T, t⟩ :: Γ)) Core.DataConst.opn q Ts ->
  Intermediate.Query Γ Core.DataConst.opn q Ts
:= by
  intro h
  induction h
  case _ => apply VecTyping.nil
  case _ h1 h2 ih =>
    apply VecTyping.cons
    simp [Intermediate.lookup_ctor?] at h1;
    split at h1 <;> try simp at h1;
    case _ bsp =>
      simp [Intermediate.lookup_ctor?]; simp [bsp];
      simp[Option.getD_eq_iff] at h1; rcases h1 with ⟨ent, lk, h1⟩; simp [Intermediate.lookup] at lk;
      cases wf; case _ wftl wfhd =>
      cases wfhd
      split at lk
      case _ e => subst e; cases lk; case _ lk _ => exfalso; simp [Intermediate.Entry.ctor?] at h1
      simp [lk]; apply h1
    apply ih



theorem Intermediate.Query.opn_strengthen_class {Γ : Intermediate.GlobalEnv}
  (wf : ⊢ (Intermediate.Global.classDecl ⟨s, n, K, fds, scs, mths⟩ :: Γ)) :
  Intermediate.Query ((Intermediate.Global.classDecl ⟨s, n, K, fds, scs, mths⟩ :: Γ)) Core.DataConst.opn q Ts ->
  Intermediate.Query Γ Core.DataConst.opn q Ts
:= by
  intro h
  induction h
  case _ => apply VecTyping.nil
  case _ h1 h2 ih =>
    apply VecTyping.cons
    simp [Intermediate.lookup_ctor?] at h1;
    split at h1 <;> try simp at h1;
    case _ bsp =>
      simp [Intermediate.lookup_ctor?]; simp [bsp];
      simp[Option.getD_eq_iff] at h1; rcases h1 with ⟨ent, lk, h1⟩; simp [Intermediate.lookup] at lk;
      cases wf; case _ wftl wfhd =>
      cases wfhd
      split at lk
      case _ e => subst e; cases lk; case _ lk _ => exfalso; simp [Intermediate.Entry.ctor?] at h1
      split at lk
      simp[lk]; apply h1
      case _ lk1 =>
      split at lk;
      cases lk; simp [Intermediate.Entry.ctor?] at h1
      simp [lk]; apply h1
    apply ih


theorem mk_inst_mth_SI_sound {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mth_SI Γ' C iname τ tm = .ok i ->
  ∃ n v na nb, i = ⟨1, #(⟨iname, n, v, na, nb⟩), tm⟩
:= by
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
  case _ mτs mn tm ts ih =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨insts', h, h1⟩
    split at h1 <;> try simp at h1
    case _ i h2 =>
    simp [List.findIdx?_eq_some_iff_getElem] at h2
    rcases h2 with ⟨hi, h2, h3⟩
    simp [List.getElem?_eq_getElem hi] at h1
    simp [h2, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨p, h1, h4⟩; subst h4;
    replace h1 := mk_inst_mth_SI_sound h1
    sorry

    -- rcases h1 with ⟨mn, b, h1, h2⟩; subst h2
    -- simp at p_in_insts; cases p_in_insts
    -- case _ h =>
    --   subst h; exists mn; replace h1 := mk_inst_mth_SI_sound h1; rcases h1 with ⟨p, h1⟩;
    --   simp at h1; rcases h1 with ⟨e, b⟩
    --   subst e; rcases b with ⟨n, v, na, nb⟩; subst b; simp
    -- case _ h2 => apply ih h h2

theorem mk_inst_mths_SI_indexing
{Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths_SI Γ' C iname mτs ts  = .ok insts ->
  (∀ i : Nat, (hi : i < mτs.length) -> ∃ j, ∃ (h : j < insts.length),
    insts[j].1 = mτs[i].1 ∧ insts[j].2.1 = mτs[i].2.2.2.2.2.1)
:= by
 intro h j hj
 fun_induction mk_inst_mths_SI generalizing insts <;> simp [pure] at h
 cases h; simp; sorry
 simp [bind, Except.bind_eq_ok_iff] at h;
 sorry

theorem lookup_SI_odata {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}
  {K : Vec Core.Kind nc} :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup cls G = Surface.Entry.odata cls K mτs ->
  ∃ mτs', Intermediate.lookup cls G' = Intermediate.Entry.odata cls K mτs'
:= by
  intro h1 h2
  fun_induction translate_SI generalizing G' <;> simp [Surface.lookup, pure] at h2
  case _ s _ _ _ ih => -- data
    simp [bind] at h1;
    split at h2
    · subst cls; simp at h2
    · simp [Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
      split at h3 <;> try simp at *
      case _ e =>
        replace e : (cls = s) = False := by grind
        cases h3; simp [Intermediate.lookup, ite_cond_eq_false (h := e)];
        replace h2 := Vec.fold_or h2
        cases h2;
        case _ h =>
          replace ih := ih h1 h; rcases ih with ⟨mτs', ih⟩
          simp [ih, Vec.foldl_or_some_default]
        case _ h => rcases h with ⟨i, h⟩; simp [Vec.get_to] at h
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    split at h2
    subst cls; simp at h2
    rcases h1 with ⟨Γ', h1, h3⟩; split at h3 <;> simp [pure, Except.pure] at *
    subst G';
    have e : (cls = s) = False := by grind
    simp [Intermediate.lookup, ite_cond_eq_false (h := e)];
    apply ih h1 h2
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> simp at *
    subst cls; split at h3;
    · split at h3; cases h3; simp [Intermediate.lookup]; rcases h2 with ⟨e1, e2, e3, e4⟩; subst e1; simp at e3; subst e3; simp; simp at h3
    · simp at h3
    split at h2 <;> simp at *
    case _ mτs =>
    split at h3 <;> simp at *
    rcases h3 with ⟨h3, h4⟩; cases h3
    have e : (cls = s) = False := by grind
    simp [Intermediate.lookup, ite_cond_eq_false (h := e)]
    split
    apply ih h1 h2
    split;
    case _ i h5 _ _ _ h6 =>
      exfalso;
      simp [List.findIdx?_eq_some_iff_getElem] at h5; rcases h5 with ⟨hi, h5, h7⟩; simp at h6;
      rcases h6 with ⟨_, h6, h7, h8, h9⟩; subst h8; simp [List.getElem?_eq_getElem hi] at h7; simp [h7] at h5
      subst h5; grind
    apply ih h1 h2
  case _ iname _ _ _ _ _ _ _ _ _ ih =>
    split at h2 <;> simp at *
    have e : (cls = iname) = False := by grind
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> simp at *
    case _ lkiname =>
    simp [Except.bind_eq_ok_iff] at h3
    rcases h3 with ⟨cls', h3, h4⟩
    split at h4 <;> try simp at *
    case _ cls' _ mτs lkcls2 =>
    split at h4 <;> try simp at *
    case _ e =>
    rcases e with ⟨e1, _⟩; subst e1
    simp [Except.bind_eq_ok_iff] at h4; rcases h4 with ⟨mths, h4, h5⟩
    split at h5 <;> try simp at *
    cases h5;
    simp [Intermediate.lookup]; split
    contradiction
    have e : (cls = iname) = False := by grind
    apply ih h1 h2


theorem lookup_SI_data {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}
  {K : Core.Kind} :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup x G = Surface.Entry.data x K ctors ->
  Intermediate.lookup x G' = Intermediate.Entry.data x K ctors
:= by
  intro h1 h2
  fun_induction translate_SI generalizing G' <;> simp [Surface.lookup, pure] at h2
  case _ s _ _ _ ih => -- data
    split at h2 <;> simp at *
    rcases h2 with ⟨e1, e2, e3, e4⟩; subst e1; subst e2; subst e3; subst e4;
    · simp [bind, Except.bind_eq_ok_iff] at h1;
      rcases h1 with ⟨Γ', h1, h3⟩;
      split at h3 <;> try simp at *
      cases h3; simp [Intermediate.lookup]
    replace h2 := Vec.fold_or h2;
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    cases h3;
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, ite_cond_eq_false (h := e)]; cases h2
    case _ h2 => replace ih := ih h1 h2; simp [ih, Vec.foldl_or_some_default]
    case _ h2 => rcases h2 with ⟨i, h2⟩; simp [Vec.get_to] at h2
  case _ s _ _ _ ih => -- defn
    simp [bind, Except.bind_eq_ok_iff] at h1;
    split at h2
    subst s; simp at h2
    rcases h1 with ⟨Γ', h1, h3⟩; split at h3 <;> simp [pure, Except.pure] at *
    subst G';
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, ite_cond_eq_false (h := e)];
    apply ih h1 h2
  case _ s _ _ _ ih => -- classDecl
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> simp at *
    split at h2 <;> simp at *
    case _ h4 =>
    split at h3 <;> simp at *
    rcases h3 with ⟨h3, h4⟩; cases h3
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, ite_cond_eq_false (h := e)]
    split
    apply ih h1 h2
    split;
    case _ i h5 _ _ _ h6 =>
      exfalso;
      simp [List.findIdx?_eq_some_iff_getElem] at h5; rcases h5 with ⟨hi, h5, h7⟩; simp at h6;
      rcases h6 with ⟨_, h6, h7, h8, h9⟩; subst h8; simp [List.getElem?_eq_getElem hi] at h7; simp [h7] at h5
      subst h5; grind
    apply ih h1 h2
  case _ iname _ _ _ _ _ _ _ _ _ ih =>
    split at h2 <;> simp at *
    have e : (x = iname) = False := by grind
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> simp at *
    case _ lkiname =>
    simp [Except.bind_eq_ok_iff] at h3
    rcases h3 with ⟨cls', h3, h4⟩
    split at h4 <;> try simp at *
    case _ cls' _ mτs lkcls2 =>
    split at h4 <;> try simp at *
    case _ e =>
    rcases e with ⟨e1, _⟩; subst e1
    simp [Except.bind_eq_ok_iff] at h4; rcases h4 with ⟨mths, h4, h5⟩
    split at h5 <;> try simp at *
    cases h5;
    simp [Intermediate.lookup]; split
    contradiction
    have e : (x = iname) = False := by grind
    apply ih h1 h2


theorem translate_SI_lookup_none {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup x G = none ->
  Intermediate.lookup x G' = none
:= by
  intro h1 h2
  fun_induction translate_SI generalizing G' x <;> simp [Surface.lookup, pure] at h2
  case _ => -- nil
    cases h1; simp [Intermediate.lookup]
  case _ Γ ih => -- data
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> simp at *
    split at h2 <;> try simp at *
    cases h3;
    simp[Vec.fold_or_val_eq_none_idx] at h2
    rcases h2 with ⟨h2, h3⟩;
    simp [Intermediate.lookup];
    split
    case _ e => subst e; contradiction
    simp [Vec.fold_or_val_eq_none_idx]
    apply And.intro
    apply ih h1 h2
    intro i v_in_vs; replace h3 := h3 i; simp [Vec.get_to, Vec.to_get_elem]at h3; contradiction
  case _ s _ _ _ ih => -- defn
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    cases h3;
    simp [Intermediate.lookup]; split
    case _ e => subst e; simp at h2
    have e : (x = s) = False := by grind
    simp [ite_cond_eq_false (h := e)] at h2
    apply ih h1 h2
  case _ s _ mτs _ ih => -- odata
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    rcases h3 with ⟨h3, _⟩
    cases h3
    split at h2 <;> try simp at *
    split at h2 <;> simp at *
    simp [Intermediate.lookup]; case _ e _ h =>
      replace e : (x = s) = False := by grind;
      simp [ite_cond_eq_false (h := e)]
      rcases h with ⟨h, h'⟩; replace h2 := h2 x h h'; contradiction
    simp [Intermediate.lookup];
    replace e : (x = s) = False := by grind;
    simp [ite_cond_eq_false (h := e)]
    split
    case _ => apply ih h1 h2
    case _ =>
    split
    case _ h3 i hi _ _ _ _ =>
      rw[List.findIdx?_eq_some_iff_getElem] at hi; rcases hi with ⟨hi, hj, _⟩
      simp at hj;
      have lem1 : i < mτs.length := by grind
      have lem : mτs[i]'(by grind) ∈ mτs := by grind
      replace h3 := h3 (mτs[i]'(lem1)).2; rw[hj] at h3; exfalso; apply h3 lem
    case _ h3 _ h4 =>
      rw[List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, _⟩
      simp at h3;
      apply ih h1 h2

  case _ ih => -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> try simp at h2
    case _ lkiname =>
    split at h3 <;> try simp at h3
    case _ lkodata =>
    simp [Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨T, ⟨tys, h3⟩, h4⟩
    split at h4 <;> try simp at h4
    case _ e =>
    split at h4 <;> try simp at h4
    simp [Except.bind_eq_ok_iff] at h4; rcases h4 with ⟨imths, h4, h5⟩
    split at h5 <;> try simp at h5
    cases h5
    simp [Intermediate.lookup]
    split
    · case _ e => subst e; exfalso; contradiction
    · apply ih h1 h2


theorem lookup_kind_SI_some {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (h : ⟦ G ⟧ = .ok G') :
  Surface.lookup_kind G x = some K -> Intermediate.lookup_kind G' x = some K
:= by
  intro h1
  unfold Surface.lookup_kind at h1
  unfold Intermediate.lookup_kind
  generalize lki_def : Surface.lookup x G = lki at *
  generalize lkc_def : Intermediate.lookup x G' = lks at *
  cases lki <;> simp at *
  case _ v =>
  cases v <;> simp [Surface.Entry.kind] at *
  case data =>
    subst h1; have lem := Surface.lookup_name_agrees lki_def;
    simp [Surface.Entry.name] at lem; subst lem;
    have lem := lookup_SI_data h lki_def;
    cases lks <;> simp at *; rw[lkc_def] at lem; simp at lem
    rw[lkc_def] at lem; cases lem; simp [Intermediate.Entry.kind]
  case odata =>
    subst h1; have lem := Surface.lookup_name_agrees lki_def;
    simp [Surface.Entry.name] at lem; subst lem;
    have lem := lookup_SI_odata h lki_def;
    rcases lem with ⟨_, lem⟩
    cases lks <;> simp at *; rw[lkc_def] at lem; simp at lem
    rw[lkc_def] at lem; cases lem; simp [Intermediate.Entry.kind]


theorem kinding_SI_transfer {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (h : ⟦ G ⟧ = .ok G') :
  G&Δ ⊢s T : K ->  G'&Δ ⊢ T : K
| .var h1 => .var h1
| .global h1 =>.global (lookup_kind_SI_some h h1)
| .app h1 h2 => .app (kinding_SI_transfer h h1) (kinding_SI_transfer h h2)
| .arrow h1 h2 => .arrow (kinding_SI_transfer h h1) (kinding_SI_transfer h h2)
| .all h1 => .all (kinding_SI_transfer h h1)
| .eq h1 h2 => .eq (kinding_SI_transfer h h1) (kinding_SI_transfer h h2)

theorem lookup_is_data_SI_some {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (h : ⟦ G ⟧ = .ok G') :
  Surface.is_data c G x -> Intermediate.is_data c G' x
:= by
  intro h1
  simp [Surface.is_data, Option.getD_eq_iff] at h1;
  rcases h1 with ⟨e, h2, h3⟩
  cases e <;> (simp [Surface.Entry.is_data] at * <;> cases c <;> simp at *)
  · simp [Intermediate.is_data, Option.getD_eq_iff];
    have lem := Surface.lookup_name_agrees h2; simp [Surface.Entry.name] at lem; subst x
    have lem := lookup_SI_data h h2; rw[lem]; simp [Intermediate.Entry.is_data]
  · simp [Intermediate.is_data, Option.getD_eq_iff];
    have lem := Surface.lookup_name_agrees h2; simp [Surface.Entry.name] at lem; subst x
    have lem := lookup_SI_odata h h2; rcases lem with ⟨_, lem⟩; rw[lem]; simp [Intermediate.Entry.is_data]


theorem Ty.data?_SI_transfer {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (h : ⟦ G ⟧ = .ok G') (T : Core.Ty) :
  Surface.Ty.data? c G T -> Intermediate.Ty.data? c G' T
 := by
 intro h1; simp [Surface.Ty.data?] at h1; split at h1 <;> simp at *;
 case _ sp => simp [Intermediate.Ty.data?]; rw[sp]; simp; apply lookup_is_data_SI_some h h1

theorem spine_kinding_SI_transfer {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (h : ⟦ G ⟧ = .ok G') (h' : (∀ T, test T -> test' T)):
  Surface.SpineKinding v x G test T ->
  Intermediate.SpineKinding v x G' test' T
| .valid h1 h2 h3 h4 h5 =>
  .valid h1
    (by intro i; have lem := h2 i;  apply kinding_SI_transfer h lem)
    (kinding_SI_transfer h h3)
    (by apply h' _ h4)
    (by intro e i; replace h5 := h5 e i; apply Ty.data?_SI_transfer h T.2.2.2.2.2.fst[i] h5)


theorem translate_SI_wf_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  ⊢ G' := by
  intro h
  fun_induction translate_SI generalizing G' <;> simp [pure, Except.pure] at *
  case _ =>
    subst h; constructor
  case _ ctors _ ih =>
    cases wf; case _ wftl wfhd =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h⟩
    split at h <;> simp at h
    subst G'; case _ h =>
    rcases h with ⟨h2, h⟩;
    simp [Vec.all_eq_true] at h;
    cases wfhd; case _ x K Γ c1 c2 c3 =>
    constructor
    · apply Intermediate.GlobalWf.data
      · intro i y T h3; replace c3 := c3 i y T h3
        rcases c3 with ⟨c3a, c3b, c3c⟩;
        apply And.intro;
        have wfG : ⊢ (Surface.Global.data x K #() :: Γ) := by
          constructor; constructor; simp; simp; apply c1; apply wftl
        have lem := spine_kinding_SI_transfer (G' := Intermediate.Global.data ⟨x, K, ⟨0, #()⟩⟩ :: Γ')
                      (test' := Core.Ty.is_data x)
                      (by simp [translate_SI, bind, Except.bind_eq_ok_iff]; exists Γ';
                          apply And.intro; apply h1; split; simp [pure, Except.pure];
                          case _ e => rw[h2] at e; contradiction)
                      (by intro T h; apply h)
                      c3a
        apply lem
        apply And.intro; apply c3b; apply translate_SI_lookup_none  h1 c3c
      · apply c2
      · apply h2
    · apply ih wftl h1
  case _ ih => -- defn
    cases wf; case _ wftl wfhd =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h⟩
    split at h <;> simp at h
    case _ h2 =>
      subst G'
      cases wfhd; case _ h3 =>
      constructor
      · apply Intermediate.GlobalWf.defn
        apply kinding_SI_transfer h1 h3
        apply h2
      · apply ih wftl h1

  case _ kc s Ks mτs Γ ih =>  -- class decl
    cases wf; case _ wftl wfhd =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h2⟩
    repeat (split at h2 <;> simp at *); case _ h3 =>
    · rcases h2 with ⟨h2, h4⟩
      subst G'
      cases wfhd; case _ c1 c2 c3 =>
      constructor
      · apply Intermediate.GlobalWf.classDecl
        apply h3
        · { intro i j hi hj ne; replace c2 := c2 i j (by grind) (by grind) ne; grind }
        · intro i mn R T tys hi tsp tys_shape; replace c3 := c3 i mn R (by grind);
          simp; rcases c3 with ⟨c3a, c3b, c3c, c3d⟩;
          apply And.intro
          · simp [c3a, mk_method_om]; rw[c3a]; simp; subst tys_shape; symm;
            apply Core.Ty.mkApps_nats_spine_eta; apply tsp
          · apply And.intro; apply c3b; apply And.intro
            apply translate_SI_lookup_none h1 c3c
            apply kinding_SI_transfer h1 c3d
      · apply ih wftl h1

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
    cases wf; case _ v cls_name _ K mτs _ wftl wfhd =>
    cases wfhd; case _ _ _ _ _ _ _ rsp' Δ_def h8 h9 lks _ q1 e h3 =>
    simp at h4 h6
    simp [Option.toTM_some_eq_ok_iff, Core.Ty.mkApps_nats_spine] at cls_name;
    rcases v with ⟨cls_name', tys⟩; cases cls_name; simp at h4 h6; simp
    constructor
    · apply Intermediate.GlobalWf.inst
      · assumption
      · apply h4
      · have lem := spine_kinding_SI_transfer (test' := Intermediate.Ty.data? Core.DataConst.opn Γ') h1
                      (by intro T h; apply Ty.data?_SI_transfer h1 T h) q1
        apply lem
      · apply h7
      · intro i hi;
        have lem := mk_inst_mths_SI_sound h6
        have lem2 := mk_inst_mths_SI_indexing h6 i hi
        rcases lem2 with ⟨j, h, lem2, lem3⟩
        exists j; exists h; apply And.intro
        symm; assumption
        replace lem := lem mths[j] (by simp);
        rcases lem with ⟨mn, n, na, nb, v, t, lem⟩; rw[lem]; simp
        rw[lem] at lem3; simp at lem3; symm; assumption
    · apply ih wftl h1



theorem Intermediate.Query.strength_inst1 {Γ : Intermediate.GlobalEnv} :
  Intermediate.Query (.cons (.instDecl ⟨iname, cls1, na, nb, nc, KsU, KsE , Tys , fds , scs, mths⟩) Γ) v #(q) #(T) ->
  T.spine = some (cls2, tys) ->
  q ≠ iname ->
  Intermediate.Query Γ v #(q) #(T)
:= by
  intro h1 h2 h3
  cases h1; case _ h1 h4 =>
  simp [Intermediate.lookup_ctor?, h2, Intermediate.lookup_ctor?, Intermediate.lookup] at h1;
  constructor
  have lem : (q = iname) = False := by grind;
  generalize ite_def : (if q = iname then
              some
                (Intermediate.Entry.octor iname
                  ⟨na, (KsU, ⟨nb, (KsE, ⟨nc, (Tys, (gt#cls1).mkApps_nats (List.range na).reverse)⟩)⟩)⟩)
            else Intermediate.lookup q Γ) = ite at *
  conv at ite_def =>
    lhs
    simp [ite_cond_eq_false (h := by apply lem)]
  simp [Intermediate.lookup_ctor?, h2, ite_def]; apply h1
  constructor



theorem Intermediate.lookup_openm_shape {G : Intermediate.GlobalEnv} (wf : ⊢ G):
  Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls spTy) ->
  ∃ na Ks1 T R tys, spTy = ⟨na, Ks1, 0, #(), 1, #(T), R⟩ ∧ T.spine = some (cls, tys)
:= by
  intro h
  induction wf
  case _ => simp [Intermediate.lookup] at h
  case _ wfhd wftl ih =>
    cases wfhd
    case data =>
      simp [Intermediate.lookup] at h; split at h
      case _ e => subst e; simp at h
      case _ =>
        replace h := Vec.fold_or h
        cases h
        case _ h => apply ih h
        case _ h => rcases h with ⟨i, h⟩; simp at h
    case defn =>
      simp [Intermediate.lookup] at h; split at h
      case _ e => subst e; simp at h
      case _ => apply ih h
    case classDecl _ s mτs na Ks1 c1 c2 c3 =>
      simp [Intermediate.lookup] at h; split at h
      case _ e => subst e; simp at h
      split at h
      apply ih h
      case _  h1 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h1
        split at h;
        · simp at h; rcases h with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3;
          case _ i _ mn spTy h2 _ =>
          rcases spTy with ⟨na', Ks1', nb', Ks2', nc', As', R⟩
          simp [List.getElem?_eq_some_iff] at h2; rcases h2 with ⟨hi, h2⟩
          let T := (Core.Ty.mkApps_nats (gt#s) ((List.range na).reverse))
          let tys := (List.range na).reverse.map (t#·)
          replace c3 := c3 i mn R T tys hi (by simp[T, tys, Core.Ty.mkApps_nats_spine]) rfl;
          rcases c3 with ⟨c3a, c3b, c3c, c3d⟩
          rw[h2] at c3a; cases c3a; simp
          rcases h1 with ⟨h1, h2, h3⟩; subst h2; simp at *
          exists na; exists Ks1; exists T; simp; exists tys
          simp [T, tys, Core.Ty.mkApps_nats_spine]
        · apply ih h
    case inst =>
      simp [Intermediate.lookup] at h; split at h
      case _ e => subst e; simp at h
      case _ => apply ih h

theorem Intermediate.lookup_openm_no_cls {G : Intermediate.GlobalEnv} (wf : ⊢ G):
  Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls spTy) ->
  Intermediate.lookup cls G = none ->
  False
:= by
  intro h1 h2
  induction wf
  simp [Intermediate.lookup] at h1
  case _ g gs wf ih =>
  cases g
  case data =>
    cases gs; case _ c1 c2 c3 =>
    simp [Intermediate.lookup] at h1 h2
    split at h1 <;> simp at *
    replace h1 := Vec.fold_or h1;
    cases h1
    case _ h1 =>
      split at h2 <;> simp at *
      simp [Vec.fold_or_val_eq_none] at h2
      rcases h2 with ⟨h2, _⟩
      apply ih h1 h2
    case _ h2 => simp at h2
  case classDecl =>
    cases gs; case _ c1 c2 =>
    simp [Intermediate.lookup] at h1 h2
    split at h1 <;> simp at *
    split at h2 <;> try simp at *
    split at h1
    case _ e =>
      split at h2
      apply ih h1 h2
      case _ h =>
        simp [List.findIdx?_eq_some_iff_getElem] at h; rcases h with ⟨hi, h, _⟩
        simp [List.getElem?_eq_getElem hi] at h2
    case _ h =>
    simp [List.findIdx?_eq_some_iff_getElem] at h; rcases h with ⟨hi, h, _⟩
    simp [List.getElem?_eq_getElem hi] at h1; rcases h1 with ⟨e1, e2, e3⟩; subst e2; contradiction
  case defn =>
    cases gs; case _ c =>
    simp [Intermediate.lookup] at h1 h2
    split at h1 <;> simp at *
    split at h2 <;> try simp at *
    apply ih h1 h2
  case instDecl =>
    cases gs
    simp [Intermediate.lookup] at h1 h2
    split at h1 <;> simp at *
    split at h2 <;> try simp at *
    apply ih h1 h2

theorem Intermediate.lookup_openm_index {G : Intermediate.GlobalEnv} (wf : ⊢ G):
  Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls spTy) ->
  Intermediate.lookup cls G = some (Intermediate.Entry.odata cls K mτs) ->
  ∃ j, ∃ (h : j < mτs.length), mτs[j].1 = mn
:= by
 intro h1 h2
 induction wf
 case _ => simp [Intermediate.lookup] at h1
 case _ wfhd wftl ih =>
 cases wfhd <;> simp [Intermediate.lookup] at h1 h2
 case data =>
   split at h1 <;> simp at *
   split at h2 <;> try simp at *;
   replace h1 := Vec.fold_or h1;
   cases h1
   case _ h1 =>
     replace h2 := Vec.fold_or h2
     cases h2
     case _ h2 => apply ih h1 h2
     case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
   case _ h1 =>
     rcases h1 with ⟨i, h1⟩; simp at h1;
 case defn =>
   split at h1 <;> simp at *
   split at h2 <;> try simp at *;
   apply ih h1 h2
 case classDecl =>
   split at h1 <;> simp at *
   split at h2 <;> try simp at *
   split at h1 <;> try simp at *
   case _ h4 _ _ e h3 =>
     subst e; simp at h2; rcases h2 with ⟨e1, e2, e3⟩; subst e1; simp at e2; subst K; subst e3;
     exfalso; apply Intermediate.lookup_openm_no_cls wftl h1 h4
   case _  c1 c2 c3 _ e i h3 =>
     subst e; simp at h2; rcases h2 with ⟨e1, e2, e3⟩; subst e1; simp at e2; subst K; subst e3;
     simp[List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨h, h3, _⟩; symm at h3
     exists i; exists h
   case _ =>
     split at h1
     case _ =>
       split at h2
       apply ih h1 h2
       case _ h3 =>
         simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, _⟩
         simp [List.getElem?_eq_getElem hi] at h2
     case _ h3 =>
       simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, _⟩
       simp [List.getElem?_eq_getElem hi] at h1; rcases h1 with ⟨h1, h2, h3⟩; subst h2; contradiction
 case inst =>
   split at h1 <;> simp at *
   split at h2 <;> try simp at *
   apply ih h1 h2


theorem Intermediate.lookup_none_ctor? :
  Intermediate.lookup s Γ = none ->
  Intermediate.lookup q Γ = some w ->
  Intermediate.Entry.ctor? s Core.DataConst.opn w = true  ->
  False
:= by
  intro h1 h2 h3
  simp [Intermediate.Entry.ctor?] at h3
  cases w <;> simp at h3
  case _ S spty =>
  rcases spty with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
  simp at h3; split at h3 <;> simp at h3
  subst h3; case _ h3 =>
  have lem : Γ&(Ks1 ++ Ks2).list.reverse ⊢ R : ★ := by sorry -- needs entry wf

  sorry



set_option maxHeartbeats 7000000
theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Ω G'
:= by
  intro h
  have wf' := translate_SI_wf_sound wf h
  intro mn na nb nc Ks1 Ks2 Ts R qs _ h1 h2
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
        replace h2 := Intermediate.Query.opn_strengthen_ctor (by constructor; apply wfhd'; apply wftl') h2
        replace ih := @ih _ wftl h3 wftl' mn h1 h2
        rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
        exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3;
        exists Ks1; exists Ks2;
        exists tys; exists fds
        exists scs; exists mths
      case _ h1 => rcases h1 with ⟨i, h1⟩; simp at h1
  case _ ih => -- defn decl
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h3, h⟩
    split at h <;> simp at *
    subst G'
    cases wf; case _ wftl wfhd =>
    cases wf'; case _ wftl' wfhd' =>
    simp [Intermediate.lookup] at h1;
    split at h1 <;> try simp at h1
    replace h2 := Intermediate.Query.opn_strengthen_defn (by constructor; apply wfhd'; apply wftl') h2
    replace ih := ih wftl h3 wftl' h1 h2
    rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
    exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3; exists Ks1; exists Ks2; exists tys; exists fds
    exists scs; exists mths
  case _ cls _ _ _ mτs _ ih => -- class Decl
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h3, h⟩
    split at h <;> simp at *
    rcases h with ⟨h, h4⟩
    subst G'
    replace h2 := Intermediate.Query.opn_strengthen_class wf' h2
    cases wf; case _ kc s _ _ _ wftl wfhd =>
    cases wf'; case _ wftl' wfhd' =>
    cases wfhd'; case _ ci1 ci2 ci3 =>
    cases wfhd; case _ cs1 cs2 cs3 =>
    simp [Intermediate.lookup] at h1
    split at h1 <;> simp at *
    split at h1 <;> simp at *
    replace ih := ih wftl h3 wftl' h1 h2
    rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
    exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3; exists Ks1; exists Ks2;
    exists tys; exists fds
    exists scs; exists mths
    split at h1 <;> simp at *
    · case _ i _ _ cls _ e =>
      rcases h1 with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3;
      rcases e with ⟨mn', spty, e3, e4, e5⟩; subst e4; simp_all;
      case _ lk =>
      simp [List.findIdx?_eq_some_iff_getElem] at lk;
      rcases lk with ⟨j, hj, lk⟩; subst hj;
      simp [List.getElem?_eq_some_iff] at e3; rcases e3 with ⟨hi, e3⟩
      rcases spty with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
      replace cs3 := cs3 i (mτs[i].fst) R hi
      let T := (Core.Ty.mkApps_nats (gt#s) ((List.range kc)).reverse)
      let tys := ((List.range kc).map (t#·)).reverse
      replace ci3 := ci3 i (mτs[i].fst) R T tys hi (by simp[T, tys, Core.Ty.mkApps_nats_spine]) (by simp [tys])
      rcases ci3 with ⟨ci3, ci4, ci5, ci6⟩; simp at ci3;
      rcases cs3 with ⟨cs3, cs4, cs5, cs6⟩
      unfold mk_method_om at ci3; rw [cs3] at ci3; simp at ci3;
      unfold mk_method_om at e5; cases e5;
      rw[cs3] at e3; cases e3
      cases qs; case _ q qs =>
      cases qs; simp at h2; cases h2; case _ h2 _ =>
      simp [Intermediate.lookup_ctor?, Core.Ty.mkApps_nats_spine] at h2;
      simp [Option.getD_eq_iff] at h2;
      rcases h2 with ⟨ent, h2, h4⟩;  -- This will be ill typed
      exfalso; apply Intermediate.lookup_none_ctor? ci1 h2 h4

    · simp_all; replace ih := ih h1;
      rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
      exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3; exists Ks1; exists Ks2;
      exists tys; exists fds
      exists scs; exists mths

  case _ cls1 iname na' Ks1' nb' Ks2' nc' As' R' ts _ ih => -- inst
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ lks q1 q2 q3 q4 =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h3⟩
    split at h3
    · simp [Option.toTM] at h3
      · split at h3 <;> simp [Except.bind_eq_ok_iff] at h3;
        case _ cls_name k1' _ mτs k2' _ _ _ _ rsp =>
        rcases h3 with ⟨cls, ⟨tys, h3⟩, h4⟩
        repeat (split at h4 <;> try simp [Except.bind_eq_ok_iff] at h4)
        case _ k1 _ _ _ _ e =>
        rcases e with ⟨e1, e'⟩; subst e1; cases h3;
        have lem := Core.Ty.mkApps_nats_spine cls_name (List.range k2').reverse
        rw[lem] at rsp; cases rsp
        rcases h4 with ⟨mths, h4, h5⟩
        split at h5 <;> simp at *
        subst G'
        cases wf'; case _ wftl' wfhd' =>
        cases wfhd'; case _ _ _ _ e _ K' _ lki1 _ _ _ _ _ lki2 _ _ _ =>
        -- cases q1;
        rw[lki2] at lki1; cases lki1;
        simp [Intermediate.lookup] at h1
        split at h1
        simp at h1

        have lem := Intermediate.lookup_openm_shape wftl' h1
        rcases lem with ⟨na, Ks1, T, R, tys, e⟩
        simp at e; rcases e with ⟨⟨e1, e2⟩, e3⟩; subst e1; simp at e2; rcases e2 with ⟨e2a, e2b, e2⟩;
        subst e2a; subst e2b; simp at e2; rcases e2 with ⟨e2a, e2b, e2⟩; subst e2a; subst e2b; simp at e2;
        rcases e2 with ⟨e2a, e2b⟩; subst e2a; subst e2b;
        cases qs; case _ q qs =>
        cases qs
        cases decEq q iname
        case _ e =>
          -- q ≠ iname
          cases decEq cls1 cls_name
          case _ e' =>
            replace e' : cls_name ≠ cls1 := by grind
            replace e : q ≠ iname := by grind
            have lem1 := Intermediate.Query.strength_inst1 h2 e3 e
            replace ih := ih wftl h wftl' h1 lem1
            rcases ih with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, As, fds, scs, mths, ih⟩
            exists i + 1; exists n; exists cls_name; exists k1; exists k2; exists k3; exists Ks1; exists Ks2
            exists As; exists fds; exists scs; exists mths
          case _ e' => -- cls = cls2
            subst e'
            replace e : q ≠ iname := by grind
            have lem1 := Intermediate.Query.strength_inst1 h2 e3 e
            replace ih := ih wftl h wftl' h1 lem1
            rcases ih with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, As, fds, scs, mths, ih⟩
            exists i + 1; exists n; exists cls_name; exists k1; exists k2; exists k3; exists Ks1; exists Ks2
            exists As; exists fds; exists scs; exists mths
        case _ e => -- q = iname
          subst e
          cases decEq cls1 cls_name
          case _ e => -- cls1 ≠ cls_name
            exfalso
            cases h2; case _ h1 h2 =>
            simp [Intermediate.lookup_ctor?] at h1; rw[e3] at h1; split at h1 <;> simp at *
            simp [Intermediate.lookup, Intermediate.Entry.ctor?] at h1; case _ e =>
            rcases e with ⟨e1, e'⟩; subst e1; subst e'
            have lem := Core.Ty.mkApps_nats_spine cls_name (List.range na').reverse
            simp [lem] at h1; cases h1; contradiction
          case _ e => -- cls1 = cls_name
            subst e
            exists 0; exists q; exists cls1; exists na'; exists nb'; exists nc'; exists Ks1'; exists Ks2';
            exists As'; exists []; exists []; exists mths; simp
            have lem := mk_inst_mths_SI_sound h4
            have lem1 := mk_inst_mths_SI_indexing h4
            have lem2 := Intermediate.lookup_openm_index wftl' h1 lki2
            rcases lem2 with ⟨j, hj, lem2⟩; subst lem2
            replace lem1 := lem1 j hj
            rcases lem1 with ⟨i, hi, lem1a, lem2a⟩
            replace lem := lem mths[i] (by grind)
            rcases lem with ⟨mn', n, na, nb, v', t, lem⟩
            exists i; exists (mths[i]).2.2.2; rw[lem]; simp
            exists #((q, ⟨n, (v', na, nb)⟩));
            apply And.intro
            grind
            constructor; grind; simp; constructor
    · simp at h3


theorem translate_IC_lookup_some_octor {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G'):
  ⟦ G ⟧ = .ok G' ->
  Core.lookup x G' = Core.Entry.octor y R ->
  Intermediate.lookup x G = Intermediate.Entry.octor y R
:= by
  intro h1 h2
  fun_induction translate_IC generalizing G' <;> simp at *
  case _ => -- nil
    simp [pure, Except.pure] at h1; subst G'; simp [Core.lookup] at h2
  case _ ih => -- data
    simp [Functor.map, Except.map] at h1;
    split at h1 <;> simp at *
    subst G'
    simp [Core.lookup] at h2;
    split at h2 <;> try simp at *
    replace h2 := Vec.fold_or h2; cases h2
    case _ h1 _ h2 =>
      cases wf; case _ wftl wfhd =>
      simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
      replace ih := ih wftl h1 h2; rw[ih]
      rw[Vec.fold_or_val_eq]
    case _ h =>
      rcases h with ⟨i, h4⟩; simp at h4
  case _ ih => -- defn
    simp [bind, Except.bind] at h1;
    split at h1 <;> simp at *
    case _ h3 =>
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    subst G'; case _ h1 =>
    simp [Core.lookup] at h2
    split at h2 <;> try simp at h2
    cases wf; case _ wftl _ =>
    simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
    apply ih wftl h3 h2
  case _ s _ _ _ _ mths _ ih =>   -- class decl
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    subst G'; case _ Γ' h1 =>
    simp [Intermediate.lookup]
    replace h2 := Core.lookup_append_some wf h2
    cases h2
    case _ h2 =>
      split
      · subst s; clear ih h1 wf;
        exfalso; induction mths <;> simp [Core.lookup] at *
        split at h2 <;> try simp at h2
        case _ ih _ => apply ih h2
      · exfalso; clear wf h1 ih; induction mths <;> simp [Core.lookup] at *
        split at h2 <;> try simp at h2
        case _ ih _ => apply ih h2
    case _ h2 =>
      rcases h2 with ⟨_, h2⟩
      simp [Core.lookup] at h2
      split at h2;
      subst x; simp at h2
      have e : (x = s) = False := by grind
      simp [ite_cond_eq_false (h := e)];
      split
      case _ =>
        have lemwf : ⊢ Γ' := by
          have lem := Core.GlobalWf.drop_wf (mths.length) wf;
          simp at lem; cases lem; case _ wftl _ => apply wftl
        apply ih lemwf h1 h2
      case _ lk _ i h =>
        simp [List.findIdx?_eq_some_iff_getElem] at h; rcases h with ⟨hi, h, h3⟩
        simp [List.getElem?_eq_getElem hi];
        generalize zdef : List.map (fun x => Core.Global.openm x.fst x.snd) mths = z at *
        have lem : z[i]'(by grind) = z[i]'(by grind) := by rfl
        conv at lem =>
          rhs
          simp only [<-zdef];
        simp [List.getElem_map] at lem; subst x;
        sorry


  case _ ih => -- inst decl
    simp [bind, Except.bind] at h1;
    split at h1 <;> try simp at h1
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    subst G'
    case _ h1 _ _ h3 =>
    simp [Intermediate.lookup];
    split
    case _ e =>
      subst e;

      -- replace h2 := Core.lookup_append  h2
      -- cases h2
      -- case _ h2 => sorry
      sorry
    sorry


theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G'):
  ⟦ G ⟧ = Except.ok G' ->
  Core.Query G' Core.DataConst.opn q Ts ->
  Intermediate.Query G Core.DataConst.opn q Ts
:= by
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
        case _ => apply translate_IC_lookup_some_octor wf h1 lk
        simp [Intermediate.Entry.ctor?, e1]
      cases h
    · cases h
    apply ih


theorem mk_inst_mth_IC_shape :
  mk_inst_mth_IC Γ' mn m p t = Except.ok i ->
  ∃ b, i = .inst mn p b
:= by
  intro h
  unfold mk_inst_mth_IC at h
  split at h <;> simp at *
  split at h <;> simp [bind] at *
  case _ e =>
    rcases e with ⟨e1, e2⟩; subst e1; subst e2
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Δ, Γ, h⟩
    simp [Functor.map, Except.map] at h; rcases h with ⟨_, h⟩
    repeat (split at h <;> simp [Option.toTM] at *)
    case _ v _ => symm at h; exists v


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
    replace ih := ih wftl h1 h2
    rcases ih with ⟨j, b, p, h1, h2⟩
    exists j + 1; exists b; exists p
  case _ ih => -- defn
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h2⟩
    simp [Functor.map, Except.map] at h2;
    split at h2 <;> simp at *
    subst G'
    cases i <;> simp at h2
    case _ i =>
    cases wf; case _ wftl _ =>
    replace ih := ih wftl h1 h2
    rcases ih with ⟨i, b, p, ih1, ih2⟩
    exists i + 1; exists b; exists p
  case _ s _ K fds scs mths _ ih => -- class
    simp [Functor.map, Except.map] at h1;
    split at h1 <;> simp at *
    case _ Γ' h3 =>
    subst G'
    cases wf; case _ wftl _ =>
    cases i <;> simp at *
    case _ i =>
    replace ih := ih wftl h3 h2
    rcases ih with ⟨i, b, p, ih1, ih2⟩;
    exists ((List.map (fun x => Core.Global.openm x.fst x.snd) mths).length + 1 + i); exists b; exists p
    have lem := List.getElem?_append_right (l₁ := List.map (fun x => Core.Global.openm x.fst x.snd) mths ++ [Core.Global.odata s (mk_cls_kind K)]) (l₂ := Γ') (i := (List.map (fun x => Core.Global.openm x.fst x.snd) mths).length + 1 + i) (by grind)
    simp at lem; grind

  case _ iname cls_name k1 k2 k3 Ks1 Ks2 tys _ _ _ _ ih => -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h2⟩
    simp [Functor.map, Except.map] at h2
    split at h2 <;> simp at *
    subst G'
    cases wf; case _ mths' mths_comp wftl wfhd =>
    cases wfhd
    rcases h3 with ⟨j1, b, p, h3, h4⟩
    cases i <;> simp at *
    case _ =>
      rcases h2 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
      subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; subst e7; subst e8; subst e9;
      subst e10; subst e11
      replace h3 := mk_inst_mths_indexing mths_comp h3
      rcases h3 with ⟨b, h3⟩;
      exists j1; exists b; exists p; grind

    case _ =>
      replace ih := ih wftl h1 h2
      rcases ih with ⟨j1, b, p, ih1, ih2⟩
      exists mths'.length + 1 + j1; exists b; exists p;
      grind

theorem lookup_IC_data {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}
  {K : Core.Kind} :
  ⟦ G ⟧ = .ok G' ->
  Intermediate.lookup x G = Intermediate.Entry.data x K ctors ->
  Core.lookup x G' = Core.Entry.data x K ctors
:= by
  intro h1 h2
  fun_induction translate_IC generalizing G' <;> simp [Intermediate.lookup] at *
  case _ s _ _ ctors _ ih =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
    subst G';
    split at h2
    · subst x; simp at h2; simp [Core.lookup]; apply h2
    · have e : (x = s) = False := by grind
      simp [Core.lookup, ite_cond_eq_false (h := e)]
      replace h2 := Vec.fold_or h2
      cases h2
      case _ h2 => have lem := ih h1 h2; simp [lem, Vec.fold_or_val_eq]
      case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3; rcases h3 with ⟨_, h3, h4⟩; subst G'
    split at h2
    · subst x; simp at h2
    · have e : (x = s) = False := by grind
      simp [Core.lookup, ite_cond_eq_false (h := e)]; apply ih h1 h2
  case _ s _ _ _ _ _ _ ih =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
    subst G'; split at h2
    · subst x; simp at h2
    · split at h2
      case _ h2 h3 =>
        simp at h3
        replace ih := ih h1 h2
        sorry
      case _ h3 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, h4⟩
        simp [List.getElem?_eq_getElem hi] at h2
  sorry




theorem lookup_IC_odata {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}
  {Ks : Vec Core.Kind kc}:
  ⟦ G ⟧ = .ok G' ->
  Intermediate.lookup x G = Intermediate.Entry.odata x Ks ctors ->
  Core.lookup x G' = Core.Entry.odata x (Core.Kind.mk_kind Ks)
  := by sorry

theorem lookup_kind_IC_some {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') :
  Intermediate.lookup_kind G x = some K -> Core.lookup_kind G' x = some K
:= by
  intro h1
  unfold Intermediate.lookup_kind at h1
  unfold Core.lookup_kind
  generalize lki_def : Intermediate.lookup x G = lki at *
  generalize lkc_def : Core.lookup x G' = lks at *
  cases lki <;> simp at *
  case _ v =>
  cases v <;> simp [Intermediate.Entry.kind] at *
  case data =>
    subst h1;
    have e := Intermediate.lookup_name_agrees lki_def; simp [Intermediate.Entry.name] at e; subst e
    have lem := lookup_IC_data h lki_def
    simp [lem] at lkc_def; subst lks; simp [Core.Entry.kind];
  case odata =>
    subst h1;
    have e := Intermediate.lookup_name_agrees lki_def; simp [Intermediate.Entry.name] at e; subst e
    have lem := lookup_IC_odata h lki_def;
    simp [lem] at lkc_def; subst lks; simp [Core.Entry.kind];

theorem lookup_is_data_IC_some {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') :
  Intermediate.is_data c G x -> Core.is_data c G' x
:= by
  intro h1
  simp [Intermediate.is_data, Option.getD_eq_iff] at h1; rcases h1 with ⟨e, h1, h2⟩
  cases e <;> (cases c <;> simp [Intermediate.Entry.is_data] at h2)
  case _ =>
    simp [Core.is_data, Option.getD_eq_iff];
    have e := Intermediate.lookup_name_agrees h1; simp [Intermediate.Entry.name] at e; subst e
    replace h1 := lookup_IC_data h h1; simp [h1, Core.Entry.is_data]
  case _ =>
    simp [Core.is_data, Option.getD_eq_iff];
    have e := Intermediate.lookup_name_agrees h1; simp [Intermediate.Entry.name] at e; subst e
    replace h1 := lookup_IC_odata h h1; simp [h1, Core.Entry.is_data]


theorem kinding_IC_transfer {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') :
  G&Δ ⊢ T : K ->  G'&Δ ⊢ T : K
| .var h1 => .var h1
| .global h1 => .global (lookup_kind_IC_some wf h h1)
| .app h1 h2 => .app (kinding_IC_transfer wf h h1) (kinding_IC_transfer wf h h2)
| .arrow h1 h2 => .arrow (kinding_IC_transfer wf h h1) (kinding_IC_transfer wf h h2)
| .all h1 => .all (kinding_IC_transfer wf h h1)
| .eq h1 h2 => .eq (kinding_IC_transfer wf h h1) (kinding_IC_transfer wf h h2)


theorem Ty.data?_transfer {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') (T : Core.Ty) :
  Intermediate.Ty.data? c G T -> Core.Ty.data? c G' T
 := by
 intro h1; simp [Intermediate.Ty.data?] at h1; split at h1 <;> simp at *;
 case _ sp => simp [Core.Ty.data?]; rw[sp]; simp; apply lookup_is_data_IC_some wf h h1

theorem spine_kinding_IC_transfer {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') (h' : (∀ T, test T -> test' T)):
  Intermediate.SpineKinding v x G test T ->
  Core.SpineKinding v x G' test' T
| .valid h1 h2 h3 h4 h5 =>
  .valid h1
    (by intro i; have lem := h2 i;  apply kinding_IC_transfer wf h lem)
    (kinding_IC_transfer wf h h3)
    (by apply h' _ h4)
    (by intro e i; replace h5 := h5 e i; apply Ty.data?_transfer wf h T.2.2.2.2.2.fst[i] h5)


theorem translate_IC_lookup_none {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} :
  ⟦ G ⟧ = .ok G' ->
  Intermediate.lookup x G = none ->
  Core.lookup x G' = none
:= by
  intro h1 h2;
  fun_induction translate_IC generalizing G' <;> simp at *
  case _ => cases h1; simp [Core.lookup]
  case _ s _ _ ctors _ ih =>
    simp [Intermediate.lookup] at h2; split at h2; cases h2
    simp [Vec.fold_or_val_eq_none_idx] at h2; rcases h2 with ⟨h2, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h2⟩
    subst h2; simp [Core.lookup]
    case _ e =>
    replace e : (x = s) = False := by grind
    simp [ite_cond_eq_false (h := e), Vec.fold_or_val_eq_none]
    apply And.intro;
    apply ih h1 h2
    intro v v_in_vs; replace v_in_vs := Vec.getElem_of_mem v_in_vs;
    rcases v_in_vs with ⟨i, v_in_vs⟩; replace h3 := h3 i; simp at v_in_vs; replace e : (x = ctors[i].1) = False := by grind
    subst v; simp [ite_cond_eq_false (h := e)]
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    simp [Intermediate.lookup] at h2
    simp [Functor.map, Except.map_eq_ok_iff] at h3;
    rcases h3 with ⟨t', h3, hh4⟩; subst G'
    split at h2; cases h2
    replace e : (x = s) = False := by grind
    simp [Core.lookup, ite_cond_eq_false (h := e)]; apply ih h1 h2
  case _ s _ _ _ _ mths _ ih =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    simp [Intermediate.lookup] at h2
    subst G'; split at h2;
    simp at h2;
    case _ e =>
      split at h2;
        case _ h3 =>
        simp [Core.lookup_append_none]
        apply And.intro
        simp [List.findIdx?_eq_none_iff] at h3;
        · clear ih h1 h2 Γ';
          induction mths <;> simp [Core.lookup]
          case _ hd tl ih =>
          simp at h3;
          split
          subst x; have h3' := h3 hd.fst hd.snd; simp at h3';
          apply ih; intro a b i;  replace h3 := h3 a b; simp at h3; apply h3; apply Or.inr; apply i

        replace e : (x = s) = False := by grind
        simp [Core.lookup, ite_cond_eq_false (h := e)];
        apply ih h1 h2
      split at h2;
      simp at h2
      case _ h3 _ h4 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, h5⟩;
        simp [List.getElem?_eq_getElem hi] at h4
  case _ iname _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ, h1, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3; rcases h3 with ⟨h3, h4, h5⟩
    subst G'; simp [Core.lookup_append_none]
    apply And.intro
    · simp [Intermediate.lookup] at h2
      split at h2
      subst x; simp at h2
      sorry -- needs a mk_inst_mths_IC lemma
    · simp [Core.lookup]; split
      subst x; simp [Intermediate.lookup] at h2
      have e : (x = iname) = False := by grind
      simp [Intermediate.lookup, ite_cond_eq_false (h := e)] at h2;
      apply ih h1 h2


theorem translate_IC_spine_kinding {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (ht : ⟦G⟧ = Except.ok G') (lk : Intermediate.lookup s G = none) :
  Intermediate.SpineKinding (Core.SpCtorVariant.data Core.DataConst.cls) y (Intermediate.Global.data { name := s, kind := K, ctors := ⟨0, #()⟩ } :: G) (Core.Ty.is_data s) T ->
  Core.SpineKinding (Core.SpCtorVariant.data Core.DataConst.cls) y (Core.Global.data 0 s K #() :: G') (Core.Ty.is_data s) T
:= by
  intro h
  cases h; case _ m1 m2 n Δ R Ks1 Ks2 Ts h1 h2 h3 h4 h5 =>
  constructor
  apply h1
  intro i; replace h2 := h2 i;
  apply kinding_IC_transfer (G' := (Core.Global.data 0 s K #() :: G'))
    (by constructor; constructor; simp; simp; apply lk; apply wf)
    (by simp [translate_IC, Functor.map, Except.map_eq_ok_iff, ht]) h2;
  apply kinding_IC_transfer (G' := (Core.Global.data 0 s K #() :: G'))
    (by constructor; constructor; simp; simp; apply lk; apply wf)
    (by simp [translate_IC, Functor.map, Except.map_eq_ok_iff, ht])
    h3
  apply h4
  intro e i; simp at e


theorem mk_inst_mths_IC_wf_sound {G' : Core.GlobalEnv} (wf : ⊢ (Core.Global.octor iname spTy :: G')) :
  mk_inst_mths_IC (Core.Global.octor iname spTy :: G') mths =  Except.ok G1 ->
  Intermediate.lookup iname Γ = none ->
  Intermediate.lookup cls_name Γ = some (Intermediate.Entry.odata cls_name K mτs) ->
  mτs.length = mths.length ->
  (∀ (i : Nat) (hi : i < mτs.length),
    ∃ (j : Nat) (hj : j < mths.length),
      mτs[i].fst = mths[j].fst ∧ Intermediate.spine_pattern_size mτs[i].snd = Intermediate.method_pattern_size mths[j]) ->
  ⊢ (G1 ++ Core.Global.octor iname spTy :: G') := by sorry

theorem translate_IC_wf_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  ⟦ G ⟧ = .ok G' ->
  ⊢ G'
:= by
  intro h
  fun_induction translate_IC generalizing G' <;> simp [pure, bind] at h
  case _ => -- nil
    cases h; constructor
  case _ ih => -- data
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h1⟩
    cases h1
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ c1 c2 c3 =>
    apply Core.ListGlobalWf.cons
    apply Core.GlobalWf.data
    intro i y T e; replace c3 := c3 i y T e; rcases c3 with ⟨c1', c2', c3'⟩;
    apply And.intro; apply translate_IC_spine_kinding wftl h c1 c1'; apply And.intro; apply c2'; apply translate_IC_lookup_none h c3'
    apply c2
    apply translate_IC_lookup_none h c1
    apply ih wftl h
  case _ ih => -- defn
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, t', h1, h2⟩
    cases h2; simp [Option.toTM_some_eq_ok_iff] at h1;
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ lk h2 =>
    constructor
    constructor
    · apply kinding_IC_transfer wftl h h2
    · apply type_directed_translation_soundness (ih wftl h) h1
    · apply translate_IC_lookup_none h lk
    apply ih wftl h
  case _ s k1 Ks fds sds mths _ ih => -- class
    rw[Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h1⟩; simp [Except.pure] at h1; subst G';
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ c1 c2 c3 =>
    have lem : ⊢ (Core.Global.odata s (mk_cls_kind Ks) :: Γ') := by
      constructor; constructor; apply translate_IC_lookup_none h c1; apply ih wftl h

    sorry -- needs method weakening property
  case _ iname cls_name k1 k2 k3 Ks1 Ks2 As fds scs mths _ ih => -- inst
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h1, h2, h3⟩;
    cases h3;
    cases wf; case _ G wftl wfhd =>
    cases wfhd; case _ mτs h4 h5 h6 h7 h8 =>
    replace ih := ih wftl h
    have lem : Core.GlobalWf Γ' (.octor iname ⟨k1, Ks1, k2, Ks2, k3, As, (gt#cls_name).mkApps_nats (List.range k1).reverse⟩)
    := by constructor;
          · apply spine_kinding_IC_transfer wftl h (test := Intermediate.Ty.data? Core.DataConst.opn G)
            (intro T c; apply Ty.data?_transfer wftl h T c)
            apply h6 -- spine Kinding
          · apply translate_IC_lookup_none h h4
    replace ih := Core.ListGlobalWf.cons lem ih
    apply mk_inst_mths_IC_wf_sound ih h2 h4 h5 h7 h8



theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  ∃ cls, Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩)
:= by
  intro h1 h2
  have wf' := translate_IC_wf_sound wf h1
  simp at h1 h2
  fun_induction translate_IC generalizing G' mn <;> try simp at *
  case _ =>
    simp [pure, Except.pure] at h1; subst h1; simp [Core.lookup] at h2
  case _ ih =>
    cases wf; case _ wftl wfhd =>
    cases wfhd;
    simp [Functor.map, Except.map_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h2⟩; subst G'
    simp [Core.lookup] at h2; split at h2 <;> try simp at h2
    replace h2 := Vec.fold_or h2
    cases h2
    case _ h2 =>
      cases wf'; case _ wftl' wfhd' =>
      replace ih := ih wftl h1 h2 wftl'; rcases ih with ⟨cls, ih⟩;
      simp[Intermediate.lookup]; exists cls
      split
      contradiction
      rw[ih]; simp [Vec.fold_or_val_eq]
    exfalso; case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
  case _ ih =>  -- defn
    cases wf; case _ wftl _ =>
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3
    rcases h3 with ⟨t', h3, h4⟩; subst G'
    simp [Core.lookup] at h2
    split at h2 <;> try simp at h2
    cases wf'; case _ wftl' wfhd' =>
    replace ih := ih wftl h1 h2 wftl'; rcases ih with ⟨cls, ih⟩
    exists cls; simp [Intermediate.lookup]
    split
    contradiction
    apply ih
  case _ cls_name kU _ fds scs mths _ ih => -- openm
    cases wf; case _ wftl wfhd =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h2⟩; subst G'
    replace h2 := Core.lookup_append_some wf' h2
    cases h2
    case _ h2 =>
      cases wfhd; case _ c1 c2 c3 =>
      exists cls_name; simp [Intermediate.lookup]; split
      case _ e => subst e; simp at *; exfalso; sorry
      split
      exfalso; sorry
      case _ i h =>
      simp [List.findIdx?_eq_some_iff_getElem] at h; rcases h with ⟨hi, h, _⟩;
      replace c3 := c3 i mn R ((gt#cls_name).mkApps_nats (List.range kU).reverse) (List.map (t#·) (List.range kU).reverse) hi (by sorry) (by simp); rcases c3 with ⟨c3i, c3j⟩
      rw[List.getElem?_eq_getElem hi]; simp; apply And.intro; simp[c3i]; sorry
    case _ h2 =>
      simp [Core.lookup] at h2; rcases h2 with ⟨_, h2⟩;
      split at h2 <;> try simp at *
      have lem : (mn = cls_name) = False := by grind
      simp [Intermediate.lookup, ite_cond_eq_false (h := lem)];
      split
      apply ih wftl h1 h2 (by have lem := Core.GlobalWf.drop_wf (mths.length + 1) wf'; simp at lem; sorry)
      cases wfhd; case _ c1 c2 c3 =>
      case _ i h =>
      exfalso;
      simp [List.findIdx?_eq_some_iff_getElem] at h; rcases h with ⟨hi, h, _⟩; sorry



  case _ iname cls_name _ _ _ _ _ _ fds scs mths _ ih => -- inst
    simp[bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
    simp [Functor.map, Except.map] at h1
    repeat (split at h1 <;> simp at h1)
    -- simp at h1;
    subst G'
    case _ h1 =>
    cases wf; case _ wftl wfhd =>
    replace ih := @ih mn _ wftl h3
    cases wfhd;
    simp [Intermediate.lookup]; split
    exfalso; case _ e => subst e; sorry
    replace h2 := Core.lookup_append_some wf' h2;
    cases h2;
    exfalso; sorry
    case _ e h2 =>
      rcases h2 with ⟨_, h2⟩; simp [Core.lookup] at h2;
      have lem : (mn = iname) = False := by grind
      simp [ite_cond_eq_false (h := lem)] at h2;
      apply ih h2 ((by have lem := Core.GlobalWf.drop_wf (mths.length + 1) wf'; simp at lem; sorry))

theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  Ω G ->
  ⟦ G ⟧ = .ok G' ->
  Ω G'
:= by
  intro oe h1
  intro x na nb nc Ks1 Ks2 Ts R q h2 h3
  have lemwf := translate_IC_wf_sound wf h1
  have lem1 := translate_IC_lookup_openm wf h1 h2
  have lem2 := translate_IC_query lemwf h1 h3
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


theorem translate_open_exhaustive_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} {G'' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  ⟦ G' ⟧ = .ok G'' ->
  Ω G''
:= by
  intro h1 h2
  have lem : Ω G' := translate_SI_sound wf h1
  have wf' : ⊢ G' := translate_SI_wf_sound wf h1
  have lem2 : Ω G'' := translate_IC_sound wf' lem h2
  apply lem2

end Translation

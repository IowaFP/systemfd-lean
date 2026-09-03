import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Core.Metatheory.Global

import Lilac
open Lilac

namespace Core

theorem lookup_append {G1 G2 : GlobalEnv} {e : Entry} (wf : ⊢ (G1 ++ G2)):
  Core.lookup x (G1 ++ G2) = some e ->
  Core.lookup x G1 = some e ∨ (Core.lookup x G1 = none ∧ Core.lookup x G2 = some e)
:= by
  intro h1
  induction G1 generalizing G2
  · apply Or.inr;
    simp [Core.lookup] at *;
    have lem : [] ++ G2 = G2 := by grind;
    simp [lem] at h1; apply h1
  case _ hd tl ih =>
    have leme : hd :: tl ++ G2 = hd :: (tl ++ G2) := by grind
    rw[leme] at h1;
    cases hd <;> simp [lookup] at h1
    case _ n s k ctors =>
      split at h1
      case _ e => subst e; simp at h1; subst e; apply Or.inl; simp [lookup]
      case _ =>
        -- cases leme
        replace h1 := Vec.fold_or h1
        cases wf; case _ wftl wfhd =>
        cases wfhd
        -- cases h1
        -- case _ h1 =>
        --   have lem : (x = s) = False := by grind
        --   apply Or.inl; simp [lookup]; simp [ite_cond_eq_false (h := lem)];
        --   replace ih := ih h1
        --   cases ih
        --   case _ ih => simp[ih, Vec.fold_or_val_eq]
        --   case _ ih => sorry
        -- case _ h1 => sorry
        sorry
    sorry
    sorry
    sorry
    sorry
    sorry


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


theorem Intermediate.Query.opn_strengthen_ctor {Γ : Intermediate.GlobalEnv}
  (wf : ⊢ (Intermediate.Global.data ⟨s, K, ⟨n, ctors⟩⟩ :: Γ)) :
  Intermediate.Query ((Intermediate.Global.data ⟨s, K, ⟨n, ctors⟩⟩ :: Γ)) Intermediate.DataConst.opn q Ts ->
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts
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
  Intermediate.Query ((Intermediate.Global.defn ⟨s, T, t⟩ :: Γ)) Intermediate.DataConst.opn q Ts ->
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts
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
  Intermediate.Query ((Intermediate.Global.classDecl ⟨s, n, K, fds, scs, mths⟩ :: Γ)) Intermediate.DataConst.opn q Ts ->
  Intermediate.Query Γ Intermediate.DataConst.opn q Ts
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


-- theorem mk_inst_mth_SI_shape :
--   mk_inst_mth_SI Γ' mn m p t = Except.ok i ->
--   ∃ b, i = .inst mn p b := by
-- intro h
-- unfold mk_inst_mth_IC at h
-- split at h <;> simp at *
-- split at h <;> simp [bind] at *
-- case _ e =>
--   rcases e with ⟨e1, e2⟩; subst e1; subst e2
--   simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Δ, Γ, h⟩
--   simp [Functor.map, Except.map] at h; rcases h with ⟨_, h⟩
--   repeat (split at h <;> simp [Option.toTM] at *)
--   case _ v _ => symm at h; exists v

theorem translate_IC_lookup_some_octor {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
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
  cases wf; case _ wftl wfhd =>
  simp [Intermediate.lookup]; rw[ite_cond_eq_false (h := by grind)]
  apply ih wftl h3 h2
case _ ih =>   -- class decl
  simp [Functor.map, Except.map] at h1
  split at h1 <;> try simp at h1
  subst G'; case _ h1 =>
  cases wf; case _ wftl wfhd =>
    simp [Intermediate.lookup]
    split
    case _ e =>
      subst e
      have lem := Core.lookup_name_agrees h2
      simp [Core.Entry.name] at lem; subst lem
      cases wfhd
      replace h2 := Core.lookup_append sorry h2
      cases h2
      case _ h2 => sorry
      case _ h2 =>
        rcases h2 with ⟨h2, h3⟩
        sorry
  -- split
  -- case _ e =>
  --   subst e;
  --   replace h2 := Core.lookup_append h2
  --   cases h2
  --   case _ h2 =>
  --     replace h2 := Core.lookup_append h2
  --     cases h2
  --     case _ mths _ _ _ h2 =>
  --       induction mths <;> simp [Core.lookup] at *
  --       case _ t ts ih =>
  --         split at h2 <;> try simp at h2
  --         apply ih wfhd h2
  --     case _ h2 =>
  --       rcases h2 with ⟨_, h2⟩; simp [Core.lookup] at h2
  --   case _ h2 =>
  --     rcases h2 with ⟨h2, h3⟩
  --
  --     simp [Core.Entry.name] at lem; subst lem;

    sorry

  -- case _ =>
  --   split
  --   sorry
  --   case _ h3 =>
  --     simp[List.findIdx?_eq_some_iff_getElem] at h3
  --     rcases h3 with ⟨j, hj, h3⟩
  --     simp [List.getElem?_eq_getElem (h := j)];
  --     sorry

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
    cases wf; case _ wftl wfhd =>
    cases wfhd;
    -- replace h2 := Core.lookup_append  h2
    -- cases h2
    -- case _ h2 => sorry
    sorry
  sorry

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

theorem translate_SI_lookup_odata {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}
  {K : Vec Core.Kind nc} {K' : Vec Core.Kind nc'} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup cls G = Surface.Entry.odata cls K mτs ->
  Intermediate.lookup cls G' = Intermediate.Entry.odata cls K' mτs' ->
  (nc = nc') ∧ K' ≍ K
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
  subst G'; case _ h =>
  rcases h with ⟨h2, h⟩; sorry
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
  cases wf; case _ cls_name _ K mτs _ wftl wfhd =>
  cases wfhd; case _ _ _ _ _ _ _ rsp' _ _ _ lks _ q1 e _ =>
  simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1
  rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1;
  rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; subst q1
  simp [Option.toTM] at cls_name; split at cls_name <;> simp at *; simp[Except.pure] at cls_name; cases cls_name
  case _ h3 =>
  rw[rsp'] at h3; cases h3; simp at h4
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
  case classDecl tys _ na Ks1 _ _ _ =>
    simp [Intermediate.lookup] at h; split at h
    case _ e => subst e; simp at h
    case _ c1 c2 c3 c4 =>
      split at h
      apply ih h
      case _  h1 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h1
        split at h;
        · simp at h; rcases h with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3;
          case _ mn spTy h2 =>
          rcases spTy with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
          simp [List.getElem?_eq_some_iff] at h2; rcases h2 with ⟨hi, h2⟩
          replace c3 := c3 _ mn R hi; rcases c3 with ⟨c3a, c3b, c3c, c3d, c3e, c3f⟩
          rw[h2] at c3a; cases c3a; simp
          rcases h1 with ⟨h1, h2, h3⟩; subst h2; simp at *
          exists na; exists Ks1; simp; exists tys
        · apply ih h
  case inst =>
    simp [Intermediate.lookup] at h; split at h
    case _ e => subst e; simp at h
    case _ => apply ih h

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
 sorry
 sorry
 sorry
 sorry

theorem Intermediate.lookup_none_ctor? :
  Intermediate.lookup s Γ = none ->
  Intermediate.lookup q Γ = some w ->
  Intermediate.Entry.ctor? s Intermediate.DataConst.opn w = true  ->
  False
:= by
  intro h1 h2 h3
  simp [Intermediate.Entry.ctor?] at h3
  cases w <;> simp at h3
  case _ S spty =>
  rcases spty with ⟨na, Ks1, nb, Ks2, nc, As, R⟩
  simp at h3; split at h3 <;> simp at h3
  subst h3; case _ h3 =>
  have lem : Γ&(Ks1 ++ Ks2).list.reverse ⊢ R : ★ := by sorry
  cases R <;> simp [Core.Ty.spine] at h3
  rcases h3 with ⟨h3, h4⟩; subst h3; subst h4; cases lem; case _ lem =>
    simp [Intermediate.lookup_kind, h1] at lem
  sorry



set_option maxHeartbeats 7000000
theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Ω G' := by
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
  cases wf; case _ wftl wfhd =>
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
    replace ci3 := ci3 i (mτs[i].fst) R hi
    rcases cs3 with ⟨cs3a, cs3b⟩; rw[e3] at cs3a; cases cs3a;
    unfold mk_method_om at e5; cases e5;
    cases qs; case _ q qs =>
    cases qs; simp at h2; cases h2; case _ h2 _ =>
    simp [Intermediate.lookup_ctor?, Core.Ty.mkApps_nats_spine] at h2;
    simp [Option.getD_eq_iff] at h2;
    cases h2
    case _ h2 =>
    rcases h2 with ⟨h2, h4⟩;  -- This will be ill typed
    exfalso; apply Intermediate.lookup_none_ctor? ci1 h2 h4


  · simp_all; replace ih := ih h1;
    rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
    exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3; exists Ks1; exists Ks2;
    exists tys; exists fds
    exists scs; exists mths

case _ cls1 iname na Ks1 nb Ks2 nc As R _ _ ih =>
  cases wf; case _ wftl wfhd =>
  cases wfhd; case _ cls2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lks _ q1 q2 q3 =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h3⟩
  split at h3
  · simp [Option.toTM] at h3
    · split at h3 <;> simp [Except.bind] at h3
      repeat (split at h3 <;> try simp at h3)
      subst G';
      cases wf'; case _ wftl' wfhd' =>
      cases wfhd'; case _ rsp _ _ _ _ _ _ _ _ rsp' _ _ e _ _ _ _ _ lki1 e1 _ v mths_comp _ _ _ _ _ lki2 _ _ =>
      cases e; rcases e1 with ⟨e1, e2⟩; cases e1
      simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1
      rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1;
      rcases q1 with ⟨e1, q1⟩; subst e1; simp at q1; rcases q1 with ⟨e1, q1⟩; subst e1; subst q1
      rw[rsp] at rsp'; simp at rsp'; rcases rsp' with ⟨e1, e2⟩; rw[lki1] at lki2; cases lki2
      simp at lki1; simp at *;
      simp [Intermediate.lookup] at h1
      split at h1
      simp at h1
      have e := translate_SI_lookup_odata wftl h lks lki1
      rcases e with ⟨e1, e2⟩; subst e1; subst e2;
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
        cases decEq cls1 cls2
        case _ e' =>
          replace e' : cls2 ≠ cls1 := by grind
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
        cases decEq cls1 cls2
        case _ e => -- cls1 ≠ cls2
          exfalso
          cases h2; case _ h1 h2 =>
          simp [Intermediate.lookup_ctor?] at h1; rw[e3] at h1; split at h1 <;> simp at *
          simp [Intermediate.lookup, Intermediate.Entry.ctor?] at h1;
          have lem := Core.Ty.mkApps_nats_spine cls2 (List.range na).reverse
          simp [lem] at h1; case _ e' => rcases e' with ⟨e'', e'⟩; subst e''; apply e; symm; apply h1
        case _ e =>
          subst e
          exists 0; exists q; exists cls1; exists na; exists nb; exists nc; exists Ks1; exists Ks2;
          exists As; exists []; exists []; exists v; simp
          have lem := mk_inst_mths_SI_sound mths_comp
          have lem1 := mk_inst_mths_SI_indexing mths_comp
          have lem2 := Intermediate.lookup_openm_index wftl' h1 lki1
          rcases lem2 with ⟨j, hj, lem2⟩; subst lem2
          replace lem1 := lem1 j hj
          rcases lem1 with ⟨i, hi, lem1a, lem2a⟩
          replace lem := lem v[i] (by grind)
          rcases lem with ⟨mn', n, na, nb, v', t, lem⟩
          exists i; exists (v[i]).2.2.2; rw[lem]; simp
          exists #((q, ⟨n, (v', na, nb)⟩));
          apply And.intro
          grind
          constructor; grind; simp; constructor
  · simp at h3


theorem translate_IC_query {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
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
      case _ => apply translate_IC_lookup_some_octor wf h1 lk
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


theorem translate_IC_wf_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  ⟦ G ⟧ = .ok G' ->
  ⊢ G' := by sorry



theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  ∃ cls, Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) := by
intro h1 h2
have wf' := translate_IC_wf_sound wf h1
simp at h1 h2
fun_induction translate_IC generalizing G' mn <;> simp at *
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
case _ cls_name _ _ _ _ _ ih => -- openm
  cases wf; case _ wftl wfhd =>
  simp [Functor.map, Except.map_eq_ok_iff] at h1;
  rcases h1 with ⟨Γ', h1, h2⟩; subst G'
  replace h2 := Core.lookup_append wf' h2
  cases h2
  case _ h2 =>

    sorry
  case _ h2 =>
    sorry

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

case _ cls_name _ _ _ _ _ _ _ _ _ _ ih => -- inst
  simp[bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
  simp [Functor.map, Except.map] at h1
  repeat (split at h1 <;> simp at h1)
  -- simp at h1;
  subst G'
  case _ h1 =>
  cases wf; case _ wftl wfhd =>
  replace ih := @ih mn _ wftl h3
  cases wfhd;
  -- replace h2 := Core.lookup_append wf h2
  -- cases h2
  -- case _ h2 =>
  --   cases wfhd;
  --   exfalso
  --   replace h2 := Core.lookup_append h2
  --   cases h2
  --   case _ h2 => apply mk_inst_mths_IC_lookup h1 h2
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

theorem translate_IC_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  Ω G ->
  ⟦ G ⟧ = .ok G' ->
  Ω G' := by
intro oe h1
intro x na nb nc Ks1 Ks2 Ts R q h2 h3
have lem1 := translate_IC_lookup_openm wf h1 h2
have lem2 := translate_IC_query wf h1 h3
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

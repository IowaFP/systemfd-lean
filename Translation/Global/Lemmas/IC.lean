import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Core.Metatheory.Global
import Translation.Term.Lemmas

import Translation.Global.Lemmas.SI

import Lilac
open Lilac

namespace Translation.IC

theorem mk_inst_mths_IC_length {Γ : Core.GlobalEnv} :
  mk_inst_mths_IC Γ mτs mths = .ok insts ->
  mths.length = insts.length
:= by
  intro h
  fun_induction mk_inst_mths_IC generalizing insts <;> simp at *
  cases h; simp
  case _ ih e1 e =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨insts', h1, h2⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨i, h2, h3⟩; rcases e with ⟨e1, e2, e3⟩; subst e1; subst e2
    subst h3; simp; apply ih h1



theorem mk_inst_mth_IC_shape :
  mk_inst_mth_IC Γ' τ mn m p t = Except.ok i ->
  ∃ b, i = .inst mn p b
:= by
  intro h
  unfold mk_inst_mth_IC at h
  split at h <;> simp at *
  split at h <;> simp [bind] at *
  case _ e =>
    subst e
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Δ, Γ, h⟩
    simp [Functor.map, Except.map] at h; rcases h with ⟨_, h⟩
    repeat (split at h <;> simp [Option.toTM] at *)
    case _ v _ => symm at h; exists v


theorem mk_inst_sc_IC_shape :
  mk_inst_sc_IC Γ' mn m p = Except.ok i ->
  ∃ b, i = .inst mn p b
:= by
  intro h
  unfold mk_inst_sc_IC at h
  split at h <;> simp at h
  simp [bind] at h
  split at h <;> try simp at h
  simp [Except.bind_eq_ok_iff, Option.toTM_some_eq_ok_iff] at h
  rcases h with ⟨ζ, Γ, h, h1⟩
  simp [Functor.map, Except.map_eq_ok_iff] at h1
  rcases h1 with ⟨j, h1, j2⟩
  exists j.fst; symm; apply j2


theorem mk_inst_mth_IC_wf {G : Core.GlobalEnv} (wf : ⊢ G) :
  mk_inst_mth_IC G ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩ mn n p t = Except.ok i ->
  (Ks1.list ++ Ks2.list).reverse = Δ ->
  ∃ b, i = .inst mn p b ∧
  ∃ ζ Γ, Core.PatternBinders .opn G Δ n Ts p ζ Γ ∧ G&(ζ ++ Δ),Γ ⊢ b : R⟨.add Core.Ty ζ.length⟩
:= by
  intro h e
  unfold mk_inst_mth_IC at h
  split at h <;> simp at *
  split at h <;> simp [bind] at *
  case _ e1 e2 =>
  subst e2; rcases e1 with ⟨e1, e2⟩; subst e1;
  simp at e2; rcases e2 with ⟨e1, e2⟩; subst e1
  rcases e2 with ⟨e1, e2⟩; subst e1
  simp at e2; rcases e2 with ⟨e1, e2⟩; subst e1
  rcases e2 with ⟨e1, e2⟩; subst e1; subst e2
  simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨ζ, Γ, h1, h2⟩
  simp [Option.toTM_some_eq_ok_iff] at h1
  simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨b, h2, h3⟩
  subst h3
  replace h1 := Core.pattern_binders_sound h1
  replace h2 := type_directed_translation_soundness wf h2
  exists b; simp; exists ζ; exists Γ; subst e; apply And.intro
  apply h1
  apply h2



theorem mk_inst_mths_IC_lookup_none {Γ : Core.GlobalEnv} {x : String} :
  mk_inst_mths_IC Γ mτs mths = Except.ok mths' ->
  Core.lookup x mths' = none
:= by
  intro h;
  fun_induction mk_inst_mths_IC generalizing mths' <;> simp at h
  · cases h; simp [Core.lookup]
  · case _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h2⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨G, h2, h3⟩
    replace h2 := mk_inst_mth_IC_shape h2
    rcases h2 with ⟨b, h2⟩; subst h2; cases h3;
    simp [Core.lookup]; apply ih; apply h1



theorem mk_inst_scs_IC_lookup_none {Γ : Core.GlobalEnv} {x : String} :
  mk_inst_scs_IC Γ scs_τs scs = Except.ok scs' ->
  Core.lookup x scs' = none
:= by
  intro h;
  fun_induction mk_inst_scs_IC generalizing scs' <;> simp at h
  · cases h; simp [Core.lookup]
  · case _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h2⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨G, h2, h3⟩
    replace h2 := mk_inst_sc_IC_shape h2
    rcases h2 with ⟨b, h2⟩; subst h2; cases h3;
    simp [Core.lookup]; apply ih; apply h1


theorem lookup_translate_openmn_no_octor {τs : List (String × Core.SpineTy)} :
  Core.lookup x (List.map (fun x => Core.Global.openm x.1 x.2) τs) = some (Core.Entry.octor y R) -> False
:= by
  intro h
  induction τs <;> simp [Core.lookup] at *
  split at h <;> try simp at h
  case _ ih _ => apply ih h


theorem translate_IC_lookup_some_octor {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G'):
  ⟦ G ⟧ = .ok G' ->
  Core.lookup x G' = Core.Entry.octor y R ->
  Intermediate.lookup x G = Intermediate.Entry.octor y R
:= by
  intro h1 h2
  fun_induction translate_IC generalizing G' <;> simp at *
  case _ => -- nil
    simp [pure, Except.pure] at h1; subst G'; simp [Core.lookup] at h2
  case _ s _ _ ctors  _ ih => -- data
    simp [Functor.map, Except.map] at h1;
    split at h1 <;> simp at *
    subst G'
    simp [Core.lookup] at h2;
    split at h2 <;> try simp at *
    replace h2 := Vec.foldr_or h2; cases h2
    case _ h1 _ h2 =>
      cases wf; case _ wftl wfhd =>
      have e : (x = s) = False := by grind
      simp [Intermediate.lookup, e]
      simp at h2
    case _ h =>
      rcases h with ⟨hi, h4⟩;
      have e : (x = s) = False := by grind
      simp [Intermediate.lookup, e, Vec.foldr_or_val_some]
      cases wf; case _ wf _ =>
      apply And.intro
      have e := Core.lookup_name_agrees h4; simp [Core.Entry.name] at e; subst e;
      apply ih wf; assumption; apply h4
      intro i h5;
      generalize zdef : Vec.map (fun x_1 => if x = x_1.1.fst then some (Core.Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none)
          ctors.zipIdx = z at *
      have lem : z[i] = z[i] := rfl
      conv at lem =>
        lhs
        rw[<-zdef]
      simp [h5] at lem; replace hi := hi z[i] Vec.getElem_mem; rw[<-lem] at hi; simp at hi

  case _ s _ _ _ ih => -- defn
    simp [bind, Except.bind] at h1;
    split at h1 <;> simp at *
    case _ h3 =>
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    subst G'; case _ h1 =>
    simp [Core.lookup] at h2
    split at h2 <;> try simp at h2
    cases wf; case _ wftl _ =>
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, e]
    apply ih wftl h3 h2

  case _ s _ _ fds scs mths _ ih =>   -- class decl
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    subst G'; case _ Γ' h1 =>
    simp [Intermediate.lookup]
    replace h2 := Core.lookup_append_some wf h2
    cases h2
    case _ h2 =>
      split
      · subst s; exfalso; apply lookup_translate_openmn_no_octor h2
      · exfalso; apply lookup_translate_openmn_no_octor h2
    case _ h2 =>
      rcases h2 with ⟨h3, h2⟩
      let wf' := Core.GlobalWf.drop_wf mths.length wf; simp at wf'
      replace h2 := Core.lookup_append_some wf' h2
      simp [Core.lookup] at h2
      cases h2
      case _ h2 =>
        exfalso;
        have e := Core.lookup_name_agrees h2; simp [Core.Entry.name] at e; subst e;
        apply lookup_translate_openmn_no_octor h2
      case _ h2 =>
        rcases h2 with ⟨h2, h4⟩
        split at h4
        case _ e =>
          subst s; simp at h4
        case _ =>
          have e : (x = s) = False := by grind
          simp [e]
          have e := Core.lookup_name_agrees h4; simp [Core.Entry.name] at e; subst e;
          split
          · split
            case _ =>
              have lemwf : ⊢ Γ' := by
                have lem := Core.GlobalWf.drop_wf mths.length wf;
                simp at lem;
                have lem := Core.GlobalWf.drop_wf scs.length lem;
                simp at lem
                cases lem; case _ wftl _ => apply wftl
              apply ih lemwf h1 h4
            case _ i h5 =>
            simp [List.findIdx?_eq_some_iff_getElem] at h5;
            rcases h5 with ⟨hi, h5, h6⟩
            simp [List.getElem?_eq_getElem hi];
            generalize zdef : List.map (fun x => Core.Global.openm x.fst x.snd) scs = z at *
            have lem : z[i]'(by grind) = z[i]'(by grind) := by rfl
            conv at lem =>
              rhs
              simp only [<-zdef];
            simp [List.getElem_map] at lem; subst y;
            have lem2 : z[i]? = Core.Global.openm scs[i].fst scs[i].snd := by grind
            apply Core.lookup_none_idx_some_contra lem2 h2
          case _ i h5 =>
            simp [List.findIdx?_eq_some_iff_getElem] at h5;
            rcases h5 with ⟨hi, h5, h6⟩
            simp [List.getElem?_eq_getElem hi];
            generalize zdef : List.map (fun x => Core.Global.openm x.fst x.snd) mths = z at *
            have lem : z[i]'(by grind) = z[i]'(by grind) := by rfl
            conv at lem =>
              rhs
              simp only [<-zdef];
            simp [List.getElem_map] at lem; subst y;
            have lem2 : z[i]? = Core.Global.openm mths[i].fst mths[i].snd := by grind
            apply Core.lookup_none_idx_some_contra lem2 h3

  case _ iname cls_name _ _ _ _ _ _ fds scs mths _ ih => -- inst decl
    simp [bind, Except.bind] at h1;
    split at h1 <;> try simp at h1
    case _ h3 =>
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    case _ scs_τs mτs h4 =>
    split at h1 <;> try simp at h1
    case _ h5 =>
    subst h5
    split at h1 <;> try simp at h1
    case _ mths' h6 =>
    split at h1 <;> try simp at h1
    case _ scs' h7 =>
    subst G'
    simp [Intermediate.lookup];
    split
    case _ e =>
      subst e
      have e := Core.lookup_name_agrees h2; simp [Core.Entry.name] at e; subst e;
      replace h2 := Core.lookup_append_some wf h2
      cases h2
      case _ h2 =>
        exfalso; have lem := mk_inst_scs_IC_lookup_none h7 (x := y); simp [lem] at h2
      case _ h =>
        rcases h with ⟨_, h2⟩
        replace wf := Core.GlobalWf.drop_wf (scs'.length) wf; simp at wf
        replace h2 := Core.lookup_append_some wf h2
        cases h2
        case _ h2 =>
          exfalso; have lem := mk_inst_mths_IC_lookup_none h6 (x := y); simp [lem] at h2
        case _ h2 =>
          rcases h2 with ⟨_, h2⟩
          simp [Core.lookup] at h2; simp [h2]

    case _ =>
      have e : (x = iname) = False := by grind
      have e := Core.lookup_name_agrees h2; simp [Core.Entry.name] at e; subst e;
      replace h2 := Core.lookup_append_some wf h2
      cases h2
      case _ h2 =>
        exfalso; have lem := mk_inst_scs_IC_lookup_none h7 (x := y); simp [lem] at h2
      case _ h =>
        rcases h with ⟨_, h2⟩
        replace wf := Core.GlobalWf.drop_wf (scs'.length) wf; simp at wf
        replace h2 := Core.lookup_append_some wf h2
        cases h2
        case _ h2 =>
          exfalso; have lem := mk_inst_mths_IC_lookup_none h6 (x := y); simp [lem] at h2
        case _ h2 =>
          rcases h2 with ⟨_, h2⟩
          simp [Core.lookup, e] at h2;
          replace wf := Core.GlobalWf.drop_wf mths'.length wf; simp at wf
          cases wf; case _ wf _ =>
          apply ih wf h3 h2


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


theorem mk_inst_mths_IC_indexing {j : Nat} :
  mk_inst_mths_IC Γ mτs ms = Except.ok mths' ->
  ms[j]? = .some ⟨x, nc, p, b⟩ ->
  ∃ b', mths'[j]? = .some (Core.Global.inst (m := nc) x p b')
:= by
 intro h1 h2
 fun_induction mk_inst_mths_IC generalizing mths' j <;> simp at *
 case _ ih e1 e =>
   simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨ms', h1, i⟩
   simp [Functor.map, Except.map] at i
   split at i <;> try simp at *
   case _ h =>
   subst mths'
   rcases e with ⟨e1, e2⟩; subst e1
   cases j <;> simp at *
   case zero h4 =>
     rcases h2 with ⟨e, h2, h3⟩; subst h2; simp at h3; rcases h3 with ⟨e1, e2⟩;
     subst e1; subst e2; subst e; apply mk_inst_mth_IC_shape h
   case succ n =>
   apply ih h1 h2

theorem mk_inst_scs_IC_indexing {j : Nat} :
  mk_inst_scs_IC Γ mτs ms = Except.ok scs' ->
  ms[j]? = .some ⟨x, nc, p⟩ ->
  ∃ b', scs'[j]? = .some (Core.Global.inst (m := nc) x p b')
:= by
 intro h1 h2
 fun_induction mk_inst_scs_IC generalizing scs' j <;> simp at *
 case _ ih e1 e =>
   simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨ms', h1, i⟩
   simp [Functor.map, Except.map] at i
   split at i <;> try simp at *
   case _ h =>
   subst scs'
   rcases e with ⟨⟨e1, e2⟩, e3⟩; subst e1 e2 e3
   cases j <;> simp at *
   case zero h4 =>
     rcases h2 with ⟨e, h2, h3⟩; subst h2; simp at h3; rcases h3 with ⟨e1, e2⟩;
     subst e; apply mk_inst_sc_IC_shape h
   case succ n =>
   apply ih h1 h2



theorem translate_IC_indexing_inst_scs {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} {i : Nat} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  G[i]? = some (Intermediate.Global.instDecl ⟨n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths⟩) ->
  (∃ (j1 : Nat), ∃ p, scs[j1]? = some ⟨x, nc, p⟩ ∧ Core.Query.Match q p) ->
  ∃ (i2 : Nat), ∃ b p, G'[i2]? = some (Core.Global.inst x p b) ∧ Core.Query.Match q p
:= by
  intro h1 h2 h3
  fun_induction translate_IC generalizing G' i <;> simp at *
  case _ ih =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨G', h1, h2⟩
    subst h2
    rcases h3 with ⟨j1, p, h3, h4⟩
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

  case _ s _ K fds' scs' mths' _ ih => -- class
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h2⟩
    subst G'
    cases wf; case _ wftl wfhd =>
    cases i <;> simp at *
    case _ i =>
    replace ih := ih wftl h1 h2
    rcases ih with ⟨i, b, p, ih1, ih2⟩;
    cases wfhd;
    case _ c1 c2 c3 c4 c5 c6 =>
    generalize mthdef : List.map (fun x => Core.Global.openm x.fst x.snd) mths' = mths''  at *
    generalize scsdef : (List.map (fun x => Core.Global.openm x.fst x.snd) scs') = scs'' at *
    generalize zdef : Core.Global.odata s (mk_cls_kind K) :: Γ' = Γ'' at *
    exists (mths''.length + (scs''.length + (1 + i)))
    have lemi : i < Γ'.length := by simp [List.getElem?_eq_some_iff] at ih1; rcases ih1 with ⟨h, _⟩; apply h;
    have lem : mths''.length ≤ mths''.length + scs''.length + scs''.length + (1 + i) := by omega
    exists b; exists p;
    simp [List.getElem?_eq_some_iff];
    apply And.intro
    · simp [<-zdef]; constructor;  -- exists
      · grind
      · omega
    · apply ih2

  case _ iname cls_name k1 k2 k3 Ks1 Ks2 tys _ _ _ _ ih => -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map] at h3
    split at h3 <;> try simp at h3
    case _ lki_cls =>
    split at h3 <;> try simp at h3
    case _ cls_name _ _ _ e =>
    subst e
    simp [Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨mthsΓ, h3, h4⟩
    simp [Except.map_eq_ok_iff] at h4; rcases h4 with ⟨scsΓ, h4, h5⟩
    generalize Γdef : (Core.Global.octor iname ⟨k1, (Ks1, ⟨k2, (Ks2, ⟨k3, (tys, (gt#cls_name).mkApps_nats (List.map (fun x => x + k2) (List.range k1)).reverse)⟩)⟩)⟩ :: Γ') = Γ'' at *
    subst G'
    cases i
    case zero =>
      simp at h2; rcases h2 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩;
      subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      rcases h3 with ⟨j, p, h6, h7⟩;
      have lem := mk_inst_scs_IC_indexing h4 h6; rcases lem with ⟨b, lem⟩
      exists j; exists b; exists p;
      simp [List.getElem?_eq_some_iff]
      simp [List.getElem?_eq_some_iff] at lem; rcases lem with ⟨h, lem⟩
      apply And.intro
      constructor;
      · have lem_len := List.getElem_append_left (as := scsΓ) (bs := (mthsΓ ++ Γ'')) (i := j)
                        (h := h) (h' := by grind);
        simp [lem_len, lem]
      · grind
      apply h7
    case succ i =>
      simp at h2
      cases wf; case _ wftl _ =>
      have lem := ih wftl h1 h2
      rcases lem with ⟨j, b, p, ih1, ih2⟩
      exists (scsΓ.length + (mthsΓ.length + (1 + j))); exists b; exists p
      apply And.intro
      · simp [<-Γdef, List.getElem?_append_right]; grind
      · apply ih2


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

  case _ s _ K fds' scs' mths' _ ih => -- class
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h2⟩
    subst G'
    cases wf; case _ wftl wfhd =>
    cases i <;> simp at *
    case _ i =>
    replace ih := ih wftl h1 h2
    rcases ih with ⟨i, b, p, ih1, ih2⟩;
    cases wfhd;
    case _ c1 c2 c3 c4 c5 c6 =>
    generalize mthdef : List.map (fun x => Core.Global.openm x.fst x.snd) mths' = mths''  at *
    generalize scsdef : (List.map (fun x => Core.Global.openm x.fst x.snd) scs') = scs'' at *
    generalize zdef : Core.Global.odata s (mk_cls_kind K) :: Γ' = Γ'' at *
    exists (mths''.length + (scs''.length + (1 + i)))
    have lemi : i < Γ'.length := by simp [List.getElem?_eq_some_iff] at ih1; rcases ih1 with ⟨h, _⟩; apply h;
    have lem : mths''.length ≤ mths''.length + scs''.length + scs''.length + (1 + i) := by omega
    exists b; exists p;
    simp [List.getElem?_eq_some_iff];
    apply And.intro
    · simp [<-zdef]; constructor;
      · grind
      · omega
    · apply ih2

  case _ iname cls_name k1 k2 k3 Ks1 Ks2 tys _ _ _ _ ih => -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map] at h3
    split at h3 <;> try simp at h3
    case _ lki_cls =>
    split at h3 <;> try simp at h3
    case _ cls_name _ _ _ e =>
    subst e
    simp [Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨mthsΓ, h3, h4⟩
    simp [Except.map_eq_ok_iff] at h4; rcases h4 with ⟨scsΓ, h4, h5⟩
    generalize Γdef : (Core.Global.octor iname ⟨k1, (Ks1, ⟨k2, (Ks2, ⟨k3, (tys, (gt#cls_name).mkApps_nats (List.map (fun x => x + k2) (List.range k1)).reverse)⟩)⟩)⟩ :: Γ') = Γ'' at *
    subst G'
    cases i
    case zero =>
      simp at h2; rcases h2 with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩;
      subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      rcases h3 with ⟨j, t', p, h7, h8⟩;
      have lem := mk_inst_mths_IC_indexing h3 h7; rcases lem with ⟨b, lem⟩
      exists (scsΓ.length +j); exists b; exists p;
      simp [List.getElem?_eq_some_iff]
      simp [List.getElem?_eq_some_iff] at lem; rcases lem with ⟨h, lem⟩
      apply And.intro
      constructor;
      · have lem_len := List.getElem_append_right (as := scsΓ) (bs := (mthsΓ ++ Γ''))
                         (i := scsΓ.length + j) (by omega) (h₂ := by simp [<-Γdef]; omega)
        conv at lem_len =>
          rhs
          simp
        simp [List.getElem_append_left (as := mthsΓ) (bs := Γ'') h, lem];
      · grind
      apply h8
    case succ i =>
      simp at h2
      cases wf; case _ wftl _ =>
      have lem := ih wftl h1 h2
      rcases lem with ⟨j, b, p, ih1, ih2⟩
      exists (scsΓ.length + (mthsΓ.length + (1 + j))); exists b; exists p
      apply And.intro
      · simp [<-Γdef, List.getElem?_append_right]; grind
      · apply ih2



theorem findIdx?_none_iff_lookup_name_none {mths : List (String × Core.SpineTy)} :
  List.findIdx? (fun y => x == y.fst) mths = none <->  Core.lookup x (List.map (fun x => Core.Global.openm x.fst x.snd) mths) = none
:= by
  induction mths <;> simp [Core.lookup]
  case _ hd tl ih =>
  apply Iff.intro
  · intro h
    have e : (x = hd.fst) = False := by grind
    simp [e]; simp [<-ih]; apply h.2
  · intro h;
    split at h
    cases h
    simp [<-ih] at h; apply And.intro; assumption; apply h

theorem lookup_name_match_implies_some_contra {mths : List (String × Core.SpineTy)} :
  Core.lookup x (List.map (fun x => Core.Global.openm x.fst x.snd) mths) = some (Core.Entry.openm x mτ) ->
  ∃ i, List.findIdx? (fun y => x == y.fst) mths = some i ∧ mths[i]? = some (x, mτ)
:= by
  intro h
  induction mths <;> try simp [Core.lookup] at h
  case _ hd tl ih =>
  split at h
  case _ e =>
    subst e; simp at h; subst mτ; exists 0; simp [List.findIdx?_eq_some_iff_getElem]
  case _ e =>
    have lem := ih h
    rcases lem with ⟨i, ih⟩
    exists i + 1; simp [List.findIdx?_eq_some_iff_getElem] at ih
    simp [List.findIdx?_eq_some_iff_getElem]
    grind

theorem lookup_IC_data {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G)
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
      simp [Core.lookup, e]
      replace h2 := Vec.foldr_or h2
      cases h2
      case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
      case _ h2 =>
      cases wf; case _ wf _ =>
      have lem := ih wf h1 h2.2;
      rcases h2 with ⟨h2, h3⟩
      simp [Vec.foldr_or_val_some]
      apply And.intro
      · apply ih wf h1 h3
      · intro i h;
        generalize zdef : Vec.map (fun y => if x = y.1.fst then some (Intermediate.Entry.ctor y.1.fst y.snd y.1.snd) else none) ctors.zipIdx = z at *
        have lem : z[i] = z[i] := rfl
        conv at lem =>
          rhs
          rw[<-zdef]
        simp [h] at lem; replace h2 := h2 z[i] Vec.getElem_mem; simp [h2] at lem
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3; rcases h3 with ⟨_, h3, h4⟩; subst G'
    cases wf; case _ wf _ =>
    split at h2
    · subst x; simp at h2
    · have e : (x = s) = False := by grind
      simp [Core.lookup, e]; apply ih wf h1 h2
  case _ s _ _ _ _ mths _ ih => -- openm
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
    subst G'; split at h2
    · subst x; simp at h2
    · split at h2
      case _ h2 h3 =>
        split at h2
        case _ h4 =>
          apply Core.lookup_append_some_mpr
          apply Or.inr
          apply And.intro
          apply findIdx?_none_iff_lookup_name_none.1 h3
          apply Core.lookup_append_some_mpr
          apply Or.inr
          apply And.intro
          apply findIdx?_none_iff_lookup_name_none.1 h4
          have e : (x = s) = False := by grind
          simp [Core.lookup, e];
          cases wf; case _ wf _ => apply ih wf h1 h2
        case _ h4 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h4;
        rcases h4 with ⟨hi, h4, h5⟩
        simp [List.getElem?_eq_getElem (h := hi)] at h2
      case _ h3 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, h4⟩
        simp [List.getElem?_eq_getElem hi] at h2
  case _ iname cls_name _ _ _ _ _ _ _ _  mths _ ih =>  -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> try simp at h2
    split at h3 <;> try simp at h3
    case _ h4 =>
    split at h3 <;> try simp at h3
    case _ e =>
    subst e
    simp [Functor.map, Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨mths', h3, h5⟩
    simp [Except.map_eq_ok_iff] at h5; rcases h5 with ⟨scs', h5, h6⟩
    subst h6;
    cases wf; case _ wf wfhd =>
    apply Core.lookup_append_some_mpr
    apply Or.inr
    apply And.intro
    · clear wf wfhd ih h1
      apply mk_inst_scs_IC_lookup_none h5
    · have e : (x = iname) = False := by grind
      apply Core.lookup_append_some_mpr
      apply Or.inr;
      simp [Core.lookup, e];
      apply And.intro
      · apply mk_inst_mths_IC_lookup_none h3
      · apply ih wf h1 h2


theorem lookup_IC_odata {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}
  {Ks : Vec Core.Kind kc} (wf : ⊢ G):
  ⟦ G ⟧ = .ok G' ->
  Intermediate.lookup x G = Intermediate.Entry.odata x Ks scs mths ->
  Core.lookup x G' = Core.Entry.odata x (Core.Kind.mk_kind Ks)
:= by
  intro h1 h2
  fun_induction translate_IC generalizing G' <;> simp [Intermediate.lookup] at *
  case _ s _ _ ctors _ ih =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
    subst G';
    split at h2
    · subst x; simp at h2;
    · have e : (x = s) = False := by grind
      simp [Core.lookup, e]
      replace h2 := Vec.foldr_or h2
      cases h2
      case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
      case _ h2 =>
      cases wf; case _ wf _ =>
      have lem := ih wf h1 h2.2;
      rcases h2 with ⟨h2, h3⟩
      simp [Vec.foldr_or_val_some]
      apply And.intro
      · apply ih wf h1 h3
      · intro i h;
        generalize zdef : Vec.map (fun y => if x = y.1.fst then some (Intermediate.Entry.ctor y.1.fst y.snd y.1.snd) else none) ctors.zipIdx = z at *
        have lem : z[i] = z[i] := rfl
        conv at lem =>
          rhs
          rw[<-zdef]
        simp [h] at lem; replace h2 := h2 z[i] Vec.getElem_mem; simp [h2] at lem
  case _ s _ _ _ ih =>
    cases wf; case _ wf _ =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3; rcases h3 with ⟨_, h3, h4⟩; subst G'
    split at h2
    · subst x; simp at h2
    · have e : (x = s) = False := by grind
      simp [Core.lookup, e]; apply ih wf h1 h2

  case _ s kU _ _ _ mths _ ih => -- class
    cases wf; case _ wf wfhd =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩;
    subst G'; split at h2
    case _ e =>
      subst e; cases h2
      apply Core.lookup_append_some_mpr; apply Or.inr
      apply And.intro
      · cases wfhd; case _ c1 c2 c3 c4 c5 =>
        clear c1 c2 c3 ih
        simp [<-findIdx?_none_iff_lookup_name_none];
        intro y τ m_in_mths;
        replace m_in_mths : ∃ i : Nat, mths[i]? = some (y, τ) := by apply List.getElem?_of_mem m_in_mths
        rcases m_in_mths with ⟨i, lem⟩; simp [List.getElem?_eq_some_iff] at lem; rcases lem with ⟨hi, lem⟩;
        replace c4 := c4 i y
        sorry
      · apply Core.lookup_append_some_mpr; apply Or.inr
        apply And.intro
        · cases wfhd; case _ c1 c2 c3 c4 c5 =>
          clear c1 c2 ih
          simp [<-findIdx?_none_iff_lookup_name_none];
          intro y τ m_in_mths;
          replace m_in_mths : ∃ i : Nat, scs[i]? = some (y, τ) := by apply List.getElem?_of_mem m_in_mths
          rcases m_in_mths with ⟨i, lem⟩; simp [List.getElem?_eq_some_iff] at lem; rcases lem with ⟨hi, lem⟩;
          replace c4 := c4 i y
          sorry
        · simp [Core.lookup]; rfl

    case _ =>
      split at h2
      case _ h2 h3 =>
        split at h2
        case _ h4 =>
          apply Core.lookup_append_some_mpr
          apply Or.inr;
          apply And.intro
          apply findIdx?_none_iff_lookup_name_none.1 h3
          apply Core.lookup_append_some_mpr
          apply Or.inr;
          apply And.intro
          apply findIdx?_none_iff_lookup_name_none.1 h4
          have e : (x = s) = False := by grind
          simp [Core.lookup, e]; apply ih wf h1 h2
        case _ h4 =>
          simp [List.findIdx?_eq_some_iff_getElem] at h4; rcases h4 with ⟨hi, h4, h5⟩
          simp [List.getElem?_eq_getElem hi] at h2
      case _ h3 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, h4⟩
        simp [List.getElem?_eq_getElem hi] at h2
  case _ iname cls_name _ _ _ _ _ _ _ _  mths _ ih =>  -- inst
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> try simp at h2
    split at h3 <;> try simp at h3
    case _ h4 =>
    split at h3 <;> try simp at h3
    case _ e =>
    subst e
    simp [Functor.map, Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨mths', h3, h5⟩
    simp [Except.map_eq_ok_iff] at h5; rcases h5 with ⟨scs', h5, h6⟩
    subst G'
    apply Core.lookup_append_some_mpr
    apply Or.inr
    apply And.intro
    · apply mk_inst_scs_IC_lookup_none h5
    · have e : (x = iname) = False := by grind
      apply Core.lookup_append_some_mpr
      apply Or.inr
      apply And.intro
      · apply mk_inst_mths_IC_lookup_none h3
      · simp [Core.lookup, e]; cases wf; case _ wf _ => apply ih wf h1 h2


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
    have lem := lookup_IC_data wf h lki_def
    simp [lem] at lkc_def; subst lks; simp [Core.Entry.kind];
  case odata =>
    subst h1;
    have e := Intermediate.lookup_name_agrees lki_def; simp [Intermediate.Entry.name] at e; subst e
    have lem := lookup_IC_odata wf h lki_def;
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
    replace h1 := lookup_IC_data wf h h1; simp [h1, Core.Entry.is_data]
  case _ =>
    simp [Core.is_data, Option.getD_eq_iff];
    have e := Intermediate.lookup_name_agrees h1; simp [Intermediate.Entry.name] at e; subst e
    replace h1 := lookup_IC_odata wf h h1; simp [h1, Core.Entry.is_data]


theorem kinding_IC_transfer {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) (h : ⟦ G ⟧ = .ok G') :
  G&Δ ⊢ T : K ->  G'&Δ ⊢ T : K
| .var h1 => .var h1
| .global h1 => .global (lookup_kind_IC_some wf h h1)
| .app h1 h2 => .app (kinding_IC_transfer  wf h h1) (kinding_IC_transfer wf h h2)
| .arrow h1 h2 => .arrow (kinding_IC_transfer  wf h h1) (kinding_IC_transfer wf h h2)
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
    simp [Vec.foldr_or_val_eq_none] at h2; rcases h2 with ⟨h2, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h2⟩
    subst h2; simp [Core.lookup]
    case _ e =>
    replace e : (x = s) = False := by grind
    simp [e, Vec.foldr_or_val_eq_none]
    apply And.intro;
    apply ih h1 h2
    intro v v_in_vs; replace v_in_vs := Vec.getElem_of_mem v_in_vs;
    rcases v_in_vs with ⟨i, v_in_vs⟩;
    simp at v_in_vs;
    generalize zdef : Vec.map (fun x_1 => if x = x_1.1.fst then some (Intermediate.Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none) ctors.zipIdx  = z at *;
    replace h3 := h3 z[i] Vec.getElem_mem; subst v; simp; intro h; subst x;
    have lem : z[i] = z[i] := rfl
    conv at lem  =>
      lhs
      rw[<-zdef]
    simp at lem; simp [h3] at lem
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    simp [Intermediate.lookup] at h2
    simp [Functor.map, Except.map_eq_ok_iff] at h3;
    rcases h3 with ⟨t', h3, hh4⟩; subst G'
    split at h2; cases h2
    replace e : (x = s) = False := by grind
    simp [Core.lookup, e]; apply ih h1 h2
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
        apply findIdx?_none_iff_lookup_name_none.1 h3
        replace e : (x = s) = False := by grind
        simp [Core.lookup, e];
        split at h2
        case _ h4 =>
          apply And.intro
          apply findIdx?_none_iff_lookup_name_none.1 h4
          apply ih h1 h2
        case _ h4 =>
          simp [List.findIdx?_eq_some_iff_getElem] at h4
          rcases h4 with ⟨hi, h4, h5⟩;
          simp [List.getElem?_eq_getElem hi] at h2

      split at h2;
      simp at h2
      case _ h3 _ h4 =>
        simp [List.findIdx?_eq_some_iff_getElem] at h3; rcases h3 with ⟨hi, h3, h5⟩;
        simp [List.getElem?_eq_getElem hi] at h4
  case _ iname _ _ _ _ _ _ _ _ _ mths _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ, h1, h3⟩
    split at h3 <;> try simp at h3
    case _ h4 =>
    split at h3 <;> try simp at h3
    case _ e =>
    subst e
    simp [Functor.map, Except.bind_eq_ok_iff] at h3; rcases h3 with ⟨mths', h3, h5⟩
    simp [Except.map_eq_ok_iff] at h5; rcases h5 with ⟨scs', h5, h6⟩
    subst G'; simp [Core.lookup_append_none]
    apply And.intro
    · apply mk_inst_scs_IC_lookup_none h5
    · apply And.intro
      · simp [Intermediate.lookup] at h2
        split at h2
        subst x; simp at h2
        apply mk_inst_mths_IC_lookup_none h3
      · simp [Core.lookup]; split
        subst x; simp [Intermediate.lookup] at h2
        have e : (x = iname) = False := by grind
        simp [Intermediate.lookup, e] at h2;
        apply ih h1 h2


theorem translate_IC_spine_kinding_data {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}
  (wf : ⊢ (Intermediate.Global.data { name := s, kind := K, ctors := ⟨0, #()⟩ } :: G)) (ht : ⟦G⟧ = Except.ok G') :
  Intermediate.SpineKinding (Core.SpCtorVariant.data Core.DataConst.cls) y (Intermediate.Global.data { name := s, kind := K, ctors := ⟨0, #()⟩ } :: G) (Core.Ty.is_data s) T ->
  Core.SpineKinding (Core.SpCtorVariant.data Core.DataConst.cls) y (Core.Global.data 0 s K #() :: G') (Core.Ty.is_data s) T
:= by
  intro h
  cases h; case _ m1 m2 n Δ R Ks1 Ks2 Ts h1 h2 h3 h4 h5 =>
  constructor
  apply h1
  intro i; replace h2 := h2 i;
  apply kinding_IC_transfer (G' := (Core.Global.data 0 s K #() :: G'))
    wf
    (by simp [translate_IC, Functor.map, Except.map_eq_ok_iff, ht]) h2;
  apply kinding_IC_transfer (G' := (Core.Global.data 0 s K #() :: G'))
    wf
    (by simp [translate_IC, Functor.map, Except.map_eq_ok_iff, ht])
    h3
  apply h4
  intro e i; simp at e

theorem translate_IC_spine_kinding_odata {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv}
  (wf : ⊢ (.cons ((Intermediate.Global.classDecl ⟨s, k, K, [], [], []⟩)) G)) (ht : ⟦G⟧ = Except.ok G') :
  Intermediate.SpineKinding (Core.SpCtorVariant.openm) y (Intermediate.Global.classDecl ⟨s, k, K, [], [], []⟩ :: G) (λ _ => true) T ->
  Core.SpineKinding (Core.SpCtorVariant.openm) y (.cons (Core.Global.odata s (Core.Kind.mk_kind K)) G') (λ _ => true) T
:= by apply spine_kinding_IC_transfer wf (by simp [translate_IC, Functor.map, Except.map_eq_ok_iff]; apply And.intro; apply ht; rfl) (by simp)

theorem mk_inst_mths_IC_wf_sound {G' : Core.GlobalEnv}{mτs : List (String × Core.SpineTy)} (wf : ⊢ (Core.Global.octor iname spTy :: G')) :
  mτs.length = mths.length ->
  mk_inst_mths_IC (Core.Global.octor iname spTy :: G') mτs mths =  Except.ok G1 ->
  (∀ (i : Nat) (hi : i < mths.length) (hj : i < mτs.length),
      mτs[i].fst = mths[i].fst ∧ Intermediate.spine_pattern_size mτs[i].snd = Intermediate.method_pattern_size mths[i]) ->
  ⊢ (G1 ++ Core.Global.octor iname spTy :: G')
:= by
  intro h0 h1 hi
  fun_induction mk_inst_mths_IC generalizing G1 <;> try simp at *
  cases h1; simp; apply wf
  case _ mτs _ _ _ spTy tl ih e1 e2 =>
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨G, h1, h2⟩;
    simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨g, h2, h3⟩
    cases h3;
    subst e1; rcases e2 with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3
    have h1b := mk_inst_mth_IC_wf
         (Δ := (spTy.2.fst.list ++ spTy.2.2.2.fst.list).reverse)
         (by apply ih; apply h0; apply h1;
             intro i hj;      replace hi := hi (i + 1) (by grind)
             intro h; replace hi := hi (by simp; grind); simp at hi; apply hi)
         h2
         rfl
    rcases h1b with ⟨b, ha, ζ, Γ, hb, hc⟩; cases ha
    constructor;
    · constructor;
      · simp; apply Core.lookup_append_weaken_left;
        · apply mk_inst_mths_IC_lookup_none h1;
        · apply tl
      rfl; apply hb; apply hc
    · apply ih; apply h0; apply h1;
      intro i hj;      replace hi := hi (i + 1) (by grind)
      intro h; replace hi := hi (by simp; grind); simp at hi; apply hi


theorem mk_inst_scs_IC_wf_sound {G' : Core.GlobalEnv}{mτs : List (String × Core.SpineTy)} (wf : ⊢ (Core.Global.octor iname spTy :: G')) :
  mτs.length = mths.length ->
  mk_inst_mths_IC (Core.Global.octor iname spTy :: G') mτs mths =  Except.ok G1 ->
  (∀ (i : Nat) (hi : i < mths.length) (hj : i < mτs.length),
      mτs[i].fst = mths[i].fst ∧ Intermediate.spine_pattern_size mτs[i].snd = Intermediate.method_pattern_size mths[i]) ->
  ⊢ (G1 ++ Core.Global.octor iname spTy :: G')
:= by
  intro h0 h1 hi
  sorry


-- TODO: This is unfortunate, need a better way to organize
theorem translate_IC_spine_kinding_valid {Γ : Intermediate.GlobalEnv} {Γ' : Core.GlobalEnv} {k1 : Nat} {Ks1 : Vec Core.Kind k1} {nm : String} {spTy : Core.SpineTy} {mτs : List (String × Core.SpineTy)}
  (wf : ⊢ Γ) (ht : ⟦Γ⟧ = .ok Γ') (wf' : ⊢ (List.map (fun x => Core.Global.openm x.fst x.snd) mτs ++ Core.Global.odata s (mk_cls_kind Ks1) :: Γ'))-- should generalize over Vec of T
 :
  Intermediate.lookup s Γ = none ->
  (c1 : ∀ (i j : Nat) (hi : i < ((nm, spTy) :: mτs).length) (hj : j < ((nm, spTy) :: mτs).length),
    i ≠ j → ((nm, spTy) :: mτs)[i].fst ≠ ((nm, spTy) :: mτs)[j].fst) ->
  (c2 :
  ∀ (i : Nat) (mn : String) (τ : Core.SpineTy) (hi : i < ((nm, spTy) :: mτs).length),
    ((nm, spTy) :: mτs)[i] = (mn, τ) →
      Intermediate.SpineKinding Core.SpCtorVariant.openm mn
        (Intermediate.Global.classDecl { name := s, kcU := k1, kind := Ks1, fds := [], scs := [], mths := [] } :: Γ)
        (λ _ => true) τ) ->
  (c3 :
  ∀ (T : Core.Ty) (tys : List Core.Ty),
    T.spine = some (s, tys) →
      tys = (List.map (fun x => t#x) (List.range k1)).reverse →
        spTy = ⟨k1, (Ks1, ⟨0, (#(), ⟨1, (#(T), spTy.snd.snd.snd.snd.snd.snd)⟩)⟩)⟩ ∧
          ¬nm = s ∧ Intermediate.lookup nm Γ = none ∧ Γ&Ks1.list.reverse ⊢ spTy.snd.snd.snd.snd.snd.snd : ★) ->
  Core.SpineKinding Core.SpCtorVariant.openm nm
    (List.map (fun x => Core.Global.openm x.fst x.snd) mτs ++ (.cons (Core.Global.odata s (mk_cls_kind Ks1)) Γ')) (λ _ => true) spTy
:= by
  intro h c1 c2 c3
  sorry
  -- simp at *
  -- replace c3 := c3 ((gt#s).mkApps_nats (List.range k1).reverse) ((List.range k1).reverse.map (t#·)) (by apply Core.Ty.mkApps_nats_spine) (by simp)
  -- rcases c3 with ⟨e1, e2, e3, e4⟩
  -- replace c2 := c2 0 nm spTy (by simp) (by simp)

  -- replace c2 : Core.SpineKinding Core.SpCtorVariant.openm nm (Core.Global.odata s (mk_cls_kind Ks1) :: Γ') (fun x => true) spTy
  --    := by apply translate_IC_spine_kinding_odata (by constructor; constructor; apply h; simp; simp; sorry; apply wf) ht c2
  -- induction mτs
  -- simp; apply c2
  -- case _ hd tl ih =>
  --   simp at wf'; cases wf'; case _ wf' wfdh' =>
  --   simp;
  --   apply Core.SpineKinding.weaken_global (tst := λ _ _ => true)
  --   · constructor; apply wfdh'; apply wf'
  --   · simp
  --   · apply ih
  --     · apply wf'
  --     · have c1s := List.uniqueness_strengthen (mn := nm) (l := ((hd :: tl)).map (·.1))
  --            (by intro i j hi hj e1 e2; simp at e2;
  --                cases i;
  --                · cases j <;> simp at *
  --                  case _ j =>
  --                    cases j  <;> simp at hj;
  --                    simp at e2; apply c1 0 1 (by grind) (by grind) (by grind); simp [e2]
  --                    case _ j _ => simp at e2; apply c1 0 (j + 2) (by grind); grind; simp[e2]; simp [hj]
  --                · cases j;
  --                  case _ j =>
  --                    simp at e2; cases j; simp at e2; apply c1 0 1 (by simp) (by simp) (by simp); simp; symm; apply e2; simp at e2;
  --                    case _ j => apply c1 0 (j+2) (by simp) (by simp at hi; simp; apply hi) (by simp); simp; symm; apply e2
  --                  case _ i j => simp at e2; apply c1 (i + 1) (j + 1); grind; grind; grind; simp; simp at hj; apply hj)
  --       have c1s' := List.uniqueness_strengthen (mn := hd.1) (l := tl.map (·.1))
  --                    (by intro i j hi hj ne1 ne2;
  --                        cases i <;> cases j
  --                        apply ne1; rfl
  --                        case _ j => simp at ne2; apply c1 1 (j + 2) (by grind) (by grind) (by grind); simp; apply ne2
  --                        case _ j => simp at ne2; apply c1 1 (j + 2) (by grind) (by grind) (by grind); simp; symm; apply ne2
  --                        case _ i j => simp at ne2; apply c1 (i + 2) (j + 2) (by grind) (by grind) (by grind); simp; apply ne2)
  --       have csw := List.uniqueness_weaken (mn := nm) (l := tl.map (·.1))
  --                      (by simp; intro i hi ne;
  --                          apply c1 0 (i + 2) (by grind) (by grind) (by grind); simp; apply ne) c1s'
  --       intro i j hi hj ne1 ne2; apply csw i j; apply ne1; grind; simp; apply hi; simp; apply hj



theorem translate_IC_wf_sound {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G):
  ⟦ G ⟧ = .ok G' ->
  ⊢ G'
:= by
  intro h
  fun_induction translate_IC generalizing G' <;> simp [pure, bind] at h
  case _ => -- nil
    cases h; constructor
  case _ s _ _ ctors _ ih => -- data
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h1⟩
    cases h1
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ c1 c2 c3 =>
    apply Core.ListGlobalWf.cons
    apply Core.GlobalWf.data
    intro i y T e; replace c3 := c3 i y T e; rcases c3 with ⟨c1', c2', c3'⟩;
    apply And.intro; apply translate_IC_spine_kinding_data (by constructor; constructor; intro i; apply i.elim0; simp; apply c1; apply wftl) h c1'; apply And.intro; apply c2'; apply translate_IC_lookup_none h c3'
    apply c2
    apply translate_IC_lookup_none h c1
    apply ih wftl h
  case _ ih => -- defn
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, t', h1, h2⟩
    cases h2;
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
    cases wfhd; case _ c1 c2 c3 c4 c5 c6 =>
    have lem : ⊢ (Core.Global.odata s (mk_cls_kind Ks) :: Γ') := by
      sorry -- constructor; constructor; apply translate_IC_lookup_none h c1; apply ih wftl h
    -- have lem2 :   ∀ (i : Nat) (mn : String) (τ : Core.SpineTy) (hi : i < mths.length),
    --      Core.SpineKinding Core.SpCtorVariant.openm mn (.cons (Core.Global.odata s (Core.Kind.mk_kind Ks)) Γ') (fun x => true) τ
    --   := by intro i nm τ hi;
    --         have lem := translate_IC_spine_kinding_valid (mτs := mths) (spTy := τ) (nm := nm) (Ks1 := Ks) (s := s) wftl h
    --         sorry
    -- clear lem2;
    -- induction mths
    -- simp; apply lem
    -- case _ hd tl ih =>
    -- rcases hd with ⟨nm, spTy⟩
    -- simp;
    sorry
    -- constructor
    -- constructor
    -- · replace c4' := c4 0 nm spTy.2.2.2.2.2.2 ((gt#s).mkApps_nats (List.range k1).reverse) ((List.range k1).reverse.map (t#·)) (by simp) (by apply Core.Ty.mkApps_nats_spine) rfl; simp at c4; rcases c4' with ⟨e1, e2, e3, e4⟩;
    --   apply translate_IC_spine_kinding_valid (nm := nm) (mτs := tl) (spTy := spTy) wftl h
    --     (by apply ih;
    --         · intro i j hi hj hk; replace c2 := c2 (i+1) (j+1) (by simp; apply hi) (by simp; apply hj) (by simp; apply hk);
    --           simp at c2; apply c2
    --         · intro i mn τs hi h; replace c3 := c3 (i+1) mn τs (by simp; apply hi) (by simp; apply h); apply c3
    --         · intro i mn R T tys hi e1 e2; simp at e2
    --           replace c4 := c4 (i+1) mn R T tys (by simp; apply hi) e1 e2; simp at c4
    --           apply c4)
    --     c1 c2 c3
    --   intro T tys h1 h2; simp at e1; rw[e1]; simp; apply And.intro
    --   · symm; apply Core.Ty.mkApps_nats_spine_eta (tys := ((List.range k1).reverse)); simp [h1, h2]
    --   · apply And.intro; grind; apply And.intro; apply e3; apply e4

    -- · simp [Core.lookup_append_none];
    --   apply And.intro
    --   · replace c2 := c2 0; simp at c2;
    --     generalize zdef : List.map (fun x => Core.Global.openm x.fst x.snd) tl = z at *
    --     have c2' : ∀ (j : Nat) (hj : j < tl.length),  ¬nm = tl[j].fst := by intro j hj; replace c2 := c2 (j+1) (by simp; apply hj) (by simp); simp at c2; apply c2
    --     have lem := Core.lookup_none_if_idx_some zdef (mn := nm)
    --     apply lem
    --     intro j mn' τ h; grind
    --   · replace c4 := c4 0 nm spTy.2.2.2.2.2.2 ((gt#s).mkApps_nats (List.range k1).reverse) ((List.range k1).reverse.map (t#·)) (by simp) (by apply Core.Ty.mkApps_nats_spine) rfl
    --     simp at c4; rcases c4 with ⟨c3a, c3b, c3c⟩
    --     have e : (nm = s) = False := by grind
    --     simp [Core.lookup, e]; apply translate_IC_lookup_none h c3c.1
    -- · apply ih;
    --   · intro i j hi hj hk; replace c2 := c2 (i+1) (j+1) (by simp; apply hi) (by simp; apply hj) (by simp; apply hk);
    --     simp at c2; apply c2
    --   · intro i mn τs hi h; replace c3 := c3 (i+1) mn τs (by simp; apply hi) (by simp; apply h); apply c3
    --   · intro i mn R T tys hi e1 e2;
    --     replace c4 := c4 (i+1) mn R T tys (by simp; apply hi) e1 e2; simp at c4
    --     apply c4

  case _ iname cls_name k1 k2 k3 Ks1 Ks2 As fds scs mths G ih => -- inst
    simp [Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h1⟩;
    split at h1 <;> try simp at h1
    case _ h2 =>
    split at h1 <;> try simp at h1
    simp [Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ'', h1, h3⟩
    rcases h3 with ⟨G', h3, h4⟩;
    cases h4
    cases wf; case _ _ _ _ _ mτs lk _ wftl wfhd =>
    cases wfhd; case _ mτs h4 h5 h6 h7 h8 =>
    replace ih := ih wftl h
    have lem : Core.GlobalWf Γ' (.octor iname ⟨k1, Ks1, k2, Ks2, k3, As, (gt#cls_name).mkApps_nats ((List.range k1).map (·+k2)).reverse⟩)
    := by sorry -- constructor;
          -- · apply spine_kinding_IC_transfer wftl h (test := Intermediate.Ty.data? Core.DataConst.opn G)
          --   (intro T c; apply Ty.data?_transfer wftl h T c)
          --   apply h6
          -- · apply translate_IC_lookup_none h h4
    replace ih := Core.ListGlobalWf.cons lem ih
    -- rw[h5] at lk; cases lk;
    -- apply mk_inst_mths_IC_wf_sound (mτs := mτs) ih h7 h1
    -- intro i hi hj; replace h8 := h8 i hi; apply h8
    sorry

theorem translate_IC_lookup_openm {G : Intermediate.GlobalEnv} {G' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Core.lookup mn G' = some (Core.Entry.openm mn ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩) ->
  ∃ cls mthTy, Intermediate.lookup mn G = some (Intermediate.Entry.openm mn cls mthTy ⟨na, (Ks1, ⟨nb, (Ks2, ⟨nc, (Ts, R)⟩)⟩)⟩)
:= by
  intro h1 h2
  have wf' := translate_IC_wf_sound wf h1
  simp at h1 h2
  fun_induction translate_IC generalizing G' mn <;> try simp at *
  case _ =>
    simp [pure, Except.pure] at h1; subst h1; simp [Core.lookup] at h2
  case _ s _ _ ctors _ ih =>
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ c1 c2 c3 =>
    simp [Functor.map, Except.map_eq_ok_iff] at h1;
    rcases h1 with ⟨Γ', h1, h2⟩; subst G'
    simp [Core.lookup] at h2; split at h2 <;> try simp at h2
    replace h2 := Vec.foldr_or h2
    cases h2
    exfalso; case _ h2 => rcases h2 with ⟨i, h2⟩; simp at h2
    case _ h2 =>
      cases wf'; case _ wftl' wfhd' =>
      replace ih := ih wftl h1 h2.2 wftl'; rcases ih with ⟨cls, mthTy, ih⟩;
      simp[Intermediate.lookup]; exists cls
      split
      contradiction
      rw[ih];
      rcases h2 with ⟨h2, h3⟩
      simp [Vec.foldr_or_val_some]
      intro i h;
      generalize zdef : Vec.map (fun x => if mn = x.1.fst then some (Core.Entry.ctor x.1.fst x.snd x.1.snd) else none) ctors.zipIdx = z at *
      have lem : z[i] = z[i] := rfl
      conv at lem =>
        rhs
        rw[<-zdef]
      simp [h] at lem; replace h2 := h2 z[i] Vec.getElem_mem; simp[lem] at h2

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
      cases wfhd; case _ c1 c2 c3 c4 c5 c6 =>
      exists cls_name; exists .clsMth;
      simp [Intermediate.lookup];
      split
      case _ e => -- mn = cls_name
        exfalso;
        subst e; simp at *; exfalso;
        replace h2 := Core.lookup_some_then_idx_some h2;
        rcases h2 with ⟨i, h2⟩; simp at h2
        replace c3 := c5 i mn R ((gt#mn).mkApps_nats (List.range kU).reverse) (List.map (t#·) (List.range kU).reverse) (by grind) (by apply Core.Ty.mkApps_nats_spine) (by simp)
        rcases c3 with ⟨_, _,_⟩; contradiction
      case _ =>
        have lem := lookup_name_match_implies_some_contra h2
        rcases lem with ⟨i, lem, lem1⟩
        rw [lem]; simp; simp [List.findIdx?_eq_some_iff_getElem] at lem; rcases lem with ⟨hi, lem, h3⟩
        simp [List.getElem?_eq_getElem hi]
        apply And.intro
        · symm; assumption
        · simp [List.getElem?_eq_getElem hi] at lem1; rw[lem1]
    case _ h2 =>
      rcases h2 with ⟨h1', h2⟩
      replace wf' := Core.GlobalWf.drop_wf mths.length wf'; simp at wf'
      replace h2 := Core.lookup_append_some wf' h2
      simp [Intermediate.lookup]
      split
      case _ e => -- mn = cls_name
        exfalso; subst e
        cases h2
        case _ h2 =>
          cases wfhd; case _ c1 c2 c3 c4 c5 c6 =>
          replace h2 := lookup_name_match_implies_some_contra h2
          rcases h2 with ⟨i, h2, h3⟩; simp [List.getElem?_eq_some_iff] at h3; rcases h3 with ⟨hi, h3⟩
          replace c2 := c2 i mn
          sorry
        case _ h2 => simp [Core.lookup] at h2
      case _ =>
        cases h2
        case _ h2 =>
          exists cls_name; exists .supCls
          have lem := lookup_name_match_implies_some_contra h2
          rcases lem with ⟨i, lem, lem1⟩
          rw [lem]; simp; simp [List.findIdx?_eq_some_iff_getElem] at lem; rcases lem with ⟨hi, lem, h3⟩
          simp [List.getElem?_eq_getElem hi]
          simp [List.getElem?_eq_getElem hi] at lem1
          replace h1' := findIdx?_none_iff_lookup_name_none.2 h1'
          rw[h1']; simp; simp [lem1]
        case _ h2 =>
          replace wf' := Core.GlobalWf.drop_wf scs.length wf'; simp at wf'
          cases wf'; case _ wf' _ =>
          rcases h2 with ⟨h2, h3⟩
          rw [<-findIdx?_none_iff_lookup_name_none] at h1'
          rw [<-findIdx?_none_iff_lookup_name_none] at h2
          rw[h1']; simp; rw[h2]; simp;
          have e : (mn = cls_name) = False := by grind
          simp [Core.lookup, e] at h3;
          apply ih wftl h1 h3 wf'
  case _ iname cls_name _ _ _ _ _ _ fds scs mths _ ih => -- inst
    simp[bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h3, h1⟩
    simp [Functor.map, Except.map] at h1
    split at h1 <;> try simp at h1
    case _ h4 =>
    split at h1 <;> try simp at h1
    case _ e =>
    subst e
    simp [Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨mths', h1, h5⟩
    split at h5 <;> try simp at h5
    case _ scs' h6 =>
    subst G'
    cases wf; case _ Γ wftl wfhd =>
    replace ih := @ih mn _ wftl h3
    cases wfhd; case _ c1 c2 c3 c4 =>
    simp at h6;
    simp [Intermediate.lookup]; split
    case _ e =>
      exfalso; subst e;
      replace h2 := Core.lookup_append_some wf' h2;
      cases h2
      case _ h2 =>
        clear c2 wf' c1 c3 c4 ih;
        replace h1 := mk_inst_mths_IC_lookup_none (x := mn) h1
        replace h6 := mk_inst_scs_IC_lookup_none (x := mn) h6
        simp [h6] at h2
      case _ h2 =>
        replace h1 := mk_inst_mths_IC_lookup_none (x := mn) h1
        rcases h2 with ⟨h3, h2⟩
        replace wf' := (Core.GlobalWf.drop_wf scs'.length wf'); simp at wf';
        replace h2 := Core.lookup_append_some wf' h2;
        cases h2
        case _ h2 => simp [h1] at h2
        case _ h2 => simp [Core.lookup] at h2
    replace h2 := Core.lookup_append_some wf' h2;
    cases h2;
    case _ h2 =>
      clear c1 c2 c3 c4 ih wf';
      replace h6 := mk_inst_scs_IC_lookup_none (x := mn) h6
      simp [h6] at h2
    case _ e h2 =>
      rcases h2 with ⟨h3, h2⟩
      replace wf' := (Core.GlobalWf.drop_wf scs'.length wf'); simp at wf';
      replace h2 := Core.lookup_append_some wf' h2;
      cases h2
      case _ h2 =>
        replace h1 := mk_inst_mths_IC_lookup_none (x := mn) h1
        exfalso; simp [h1] at h2;
      case _ h2 =>
        replace e : (mn = iname) = False := by grind
        simp [Core.lookup, e] at h2;
        rcases h2 with ⟨h1, h2⟩
        replace wf' := Core.GlobalWf.drop_wf mths'.length wf'; simp at wf'
        cases wf'; case _ wf' _ =>
        apply ih h2 wf'


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
  rcases lem1 with ⟨cls, mthTy, lem1⟩
  replace oe := @oe x na nb nc Ks1 Ks2 Ts R q cls mthTy lem1 lem2
  rcases oe with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, oe1, j, oe2⟩
  cases oe2
  case _ oe2 =>
    sorry
  case _ oe2 =>
    cases oe2
    case _ oe2 =>
      have lem := translate_IC_indexing_inst_scs (i := i) wf h1 oe1 oe2
      apply lem
    case _ oe2 =>
    have lem := translate_IC_indexing_inst_mths (i := i) wf h1 oe1 oe2
    apply lem

end Translation.IC

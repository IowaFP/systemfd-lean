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

namespace Translation.SI


theorem mk_inst_mth_SI_shape {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mth_SI Γ' C iname τ tm = .ok i ->
  ∃ (pat : Core.Pattern 1) , i = ⟨1, pat, tm⟩ ∧ τ.2.2.2.2.1 = 1 ∧ τ.2.2.1 = 0 ∧
  ∃ (n : Nat) (v : Vec Core.Ty n) (na nb: Nat), pat = #(⟨iname, n, v, na, nb⟩)
:= by
  intro h
  unfold mk_inst_mth_SI at h <;> simp at h
  split at h
  case _ h =>
    split at h <;> try simp [pure, Except.pure, bind, Except.bind_eq_ok_iff] at h;
    rcases h with ⟨s, h1, b, h2, a1, b1, h3⟩;
    split at h3 <;> simp at h3
    subst i;
    case _ e =>
      rcases e with ⟨⟨e1, ⟨e2, e3⟩⟩, e4⟩; subst e1; subst e2; subst e3; subst e4; simp
  simp at h

theorem mk_superclass_om_shape {n na nb nc : Nat} {Ks : Vec Core.Kind n}
  {Ks1 : Vec Core.Kind na} {As : Vec Core.Ty nc} {Ks2 : Vec Core.Kind nb} {tys : List (Fin n)} :
  Surface.mk_superclass_om cls Ks SC tys = ⟨na, Ks1, nb, Ks2, nc, As, R⟩ ->
  n = na ∧ Ks1 ≍ Ks ∧ nb = 0 ∧ nc = 1 ∧ As ≍ #((gt#cls).mkApps_nats (List.range Ks.length).reverse)
  ∧ R = (gt#SC).mkApps_nats tys
:=
  by
  intro h
  unfold Surface.mk_superclass_om at h
  simp at h
  rcases h with ⟨e1, e2⟩; subst e1; simp at e2; grind;

theorem mk_inst_mths_SI_shape {Γ' : Intermediate.GlobalEnv} :
  ts.length = mτs.length ->
  mk_inst_mths_SI Γ' C iname mτs ts = .ok insts ->
  ∀ i ∈ insts, ∃ (mn : String) (n na nb : Nat) (v : Vec Core.Ty n) (t : Surface.Term), i = ⟨mn, 1, #(⟨iname, n, v, na, nb⟩), t⟩
:= by
  intro h h2 p p_in_insts
  fun_induction mk_inst_mths_SI generalizing insts <;> simp [pure, Except.pure] at *
  subst h2; cases p_in_insts
  case _ mτs mn tm ts _ _ ih =>
  simp [bind, Except.bind_eq_ok_iff] at h2; rcases h2 with ⟨insts', h2, h3⟩
  split at h3 <;> try simp at h3
  case _ is h4 =>
  simp [Except.bind_eq_ok_iff] at h3
  rcases h3 with ⟨hi, h3, h4⟩
  subst insts
  cases p_in_insts
  case _ =>
    replace h3 := mk_inst_mth_SI_shape h3
    rcases h3 with ⟨pat, e1, e2, e3⟩
    grind
  case _ p_in_insts => apply ih h h2 p_in_insts

theorem mk_inst_mths_SI_length {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths_SI Γ' C iname mτs ts = .ok insts ->
  mτs.length = ts.length ∧ ts.length = insts.length
:= by
  intro h
  fun_induction mk_inst_mths_SI generalizing insts
  cases h; simp
  case _ mn τ mτs mn' t ts ih =>
    simp [bind, Except.bind_eq_ok_iff] at h;
    rcases h with ⟨is, h1, h2⟩
    split at h2 <;> try simp at h2
    case _ e =>
    subst e; simp [Except.bind_eq_ok_iff] at h2; rcases h2 with ⟨m_τs, h2, h3⟩; cases h3;
    simp; apply ih h1
  cases h

theorem mk_inst_scs_SI_length {Γ : Intermediate.GlobalEnv} :
  mk_inst_scs_SI Γ C iname ts = .ok ts' ->
  ts.length = ts'.length
:= by

  sorry

theorem mk_inst_sc_SI_shape :
  mk_inst_sc_SI Γ C iname spTy = Except.ok p ->
  Intermediate.spine_pattern_size spTy = p.1
:= by
  intro h
  simp [mk_inst_sc_SI] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  simp [bind, Except.bind_eq_ok_iff] at h;
  rcases h with ⟨r_s, r_tys, h⟩; rcases h with ⟨h1, T_s, T_tys, h⟩
  rcases h with ⟨h2, h⟩; split at h <;> try simp at h
  cases h; simp


theorem mk_inst_scs_SI_shape :
  mk_inst_scs_SI Γ C iname scs_τs = .ok scs' ->
  ∀ i, (h : scs_τs.length = scs'.length) ->
  (hi : i < scs_τs.length) ->
  scs_τs[i].fst = scs'[i].fst ∧ Intermediate.spine_pattern_size scs_τs[i].snd = scs'[i].snd.fst
:= by
  intro h i h1 h2
  fun_induction mk_inst_scs_SI generalizing scs' i
  cases h2
  case _ ih =>
  simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨scs', h, h1, h2, h3⟩
  cases h3
  cases i <;> simp at *
  apply mk_inst_sc_SI_shape; assumption
  simp at h1; apply ih h
  apply h1


theorem mk_inst_mths_SI_indexing2 {Γ' : Intermediate.GlobalEnv} :
  mk_inst_mths_SI Γ' C iname mτs ts  = .ok insts ->
  (∀ (k : Nat) i τ, insts[k]? = some i -> mτs[k]? = some τ ->
    (i.1 = τ.1 ∧ i.2.1 = τ.2.2.2.2.2.1))
:= by
  intro h k hk
  fun_induction mk_inst_mths_SI generalizing insts k
  intro k i τ; cases h; cases hk; cases i
  case _ mτs ts ih =>
    simp [bind, Except.bind_eq_ok_iff] at h;
    rcases h with ⟨is, h1, h2⟩
    split at h2 <;> try simp at h2
    case _ e =>
    subst e; simp [Except.bind_eq_ok_iff] at h2; rcases h2 with ⟨m_τs, h2, h3⟩; cases h3;
    cases k <;> simp at *
    replace h2 := mk_inst_mth_SI_shape h2;
    rcases h2 with ⟨pat, h2, e1, e2, h3⟩
    grind
    apply ih h1
  cases h


theorem mk_inst_mths_SI_indexing {Γ' : Intermediate.GlobalEnv} :
  (p : mk_inst_mths_SI Γ' C iname mτs ts  = .ok insts) ->
  (∀ k : Nat, (hi : k < mτs.length) ->
    (insts[k]'(by have lem := mk_inst_mths_SI_length p; grind)).1 = mτs[k].1 ∧
    (insts[k]'(by have lem := mk_inst_mths_SI_length p; grind)).2.1 = mτs[k].2.2.2.2.2.1)
:= by
  intro h k hk
  have l := mk_inst_mths_SI_length h
  have lem :=  mk_inst_mths_SI_indexing2 h k (insts[k]) (mτs[k]) (by grind) (by grind)
  apply lem

theorem lookup_SI_odata {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv}
  {K : Vec Core.Kind nc} :
  ⟦ G ⟧ = .ok G' ->
  Surface.lookup cls G = Surface.Entry.odata cls K scs mτs ->
  ∃ scs' mτs', Intermediate.lookup cls G' = Intermediate.Entry.odata cls K scs' mτs'
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
        cases h3; simp [Intermediate.lookup, e];
        replace h2 := Vec.foldr_or h2
        cases h2;
        case _ h => rcases h with ⟨i, h⟩; simp at h
        case _ ctors _ _ h =>
          replace ih := ih h1 h.2; rcases ih with ⟨mτs', ih⟩
          rcases h with ⟨h1, h2⟩
          exists mτs';
          simp [Vec.foldr_or_val_some]
          apply And.intro
          · apply ih
          · intro i h;
            generalize zdef : Vec.map (fun y => if cls = y.1.fst
              then some (Surface.Entry.ctor y.1.fst y.snd y.1.snd) else none) ctors.zipIdx = z at *
            have lem : z[i] = z[i] := rfl
            conv at lem =>
              lhs
              rw[<-zdef]
            simp [h] at lem; replace h1 := h1 z[i] (by simp [Vec.getElem_mem]); simp [<-lem] at h1
  case _ s _ _ _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1;
    split at h2
    subst cls; simp at h2
    rcases h1 with ⟨Γ', h1, h3⟩; split at h3 <;> simp [pure, Except.pure] at *
    subst G';
    have e : (cls = s) = False := by grind
    simp [Intermediate.lookup, e];
    apply ih h1 h2

  case _ s _ scs mτs _ ih =>
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> simp at *
    subst cls; split at h3;
    · split at h3 <;> try simp at h3
      cases h3; simp [Intermediate.lookup];
      rcases h2 with ⟨e1, e2, e3, e4⟩; subst e1; simp at e3; subst e2; simp; simp at e4; apply e4.1
    · simp at h3
    split at h2 <;> try simp at h2
    case _ h4 =>
    split at h2 <;> try simp at h2
    case _ h5 =>
    split at h3 <;> simp at h3
    rcases h3 with ⟨h6, h7⟩; cases h6
    have e : (cls = s) = False := by grind
    simp [Intermediate.lookup, e]
    simp at h4 h5
    replace ih := ih h1 h2
    split
    · split
      · apply ih
      · case _ h8 i h7 =>
        simp at h7; simp [List.findIdx?_eq_some_iff_getElem] at h7; rcases h7 with ⟨h7, h9, h10⟩;
        exfalso; replace h5 := h5 (scs[i]'h7).2.1 (scs[i]'h7).2.2
        simp [h9] at h5; apply h5; grind
    · split
      · exfalso; case _ i h8 _ _ _ h9 =>
        simp at h9;
        simp [List.findIdx?_eq_some_iff_getElem] at h8
        rcases h8 with ⟨h8, h9, h10⟩
        replace h4 := h4 (mτs[i]'h8).2; simp [h9] at h4; apply h4; grind
      case _ i h8 _ _ =>
        exfalso
        simp [List.findIdx?_eq_some_iff_getElem] at h8
        rcases h8 with ⟨h8, h9, h10⟩
        replace h4 := h4 (mτs[i]'h8).2; simp [h9] at h4; apply h4; grind

  case _ iname _ _ _ _ _ _ _ _ _ ih => -- inst
    split at h2 <;> simp at *
    have e : (cls = iname) = False := by grind
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> simp at *
    case _ lkiname =>
    simp [Except.bind_eq_ok_iff] at h3
    rcases h3 with ⟨cls', h3, h4⟩
    split at h4 <;> try simp at h4
    case _ h5 =>
    split at h4 <;> try simp at h4
    case _ h6 =>
    simp [Except.bind_eq_ok_iff] at h4; rcases h4 with ⟨mths', h4, h5⟩
    split at h5 <;> try simp at h5
    cases h5
    case _ cls' _ scs' h5 =>
    rcases h5 with ⟨h5, h6⟩
    cases h6
    rcases h6 with ⟨e1, e2⟩; subst e1
    have e : (cls = iname) = False := by grind
    simp [Intermediate.lookup, e]
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
    replace h2 := Vec.foldr_or h2;
    simp [bind, Except.bind_eq_ok_iff] at h1
    rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    cases h3;
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, e]; cases h2
    case _ ctors _ _ _ h3 h2 =>
    replace ih := ih h1 h2;
    simp [Vec.foldr_or_val_some]
    apply And.intro;
    · apply ih
    · intro i h;
      generalize zdef : Vec.map (fun x_1 => if x = x_1.1.fst then some (Surface.Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none)
          ctors.zipIdx = z at *
      have lem : z[i] = z[i] := rfl
      conv at lem =>
        lhs
        rw[<-zdef]
      simp [h] at lem; replace h3 := h3 z[i] (by simp [Vec.getElem_mem]); simp [<-lem] at h3
  case _ s _ _ _ ih => -- defn
    simp [bind, Except.bind_eq_ok_iff] at h1;
    split at h2
    subst s; simp at h2
    rcases h1 with ⟨Γ', h1, h3⟩; split at h3 <;> simp [pure, Except.pure] at *
    subst G';
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, e];
    apply ih h1 h2

  case _ s _ _ _ _ ih => -- classDecl
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h2 <;> simp at *
    split at h2 <;> simp at *
    case _ h4 =>
    split at h3 <;> simp at *
    rcases h3 with ⟨h3, h4'⟩; cases h3
    split at h2 <;> try simp at h2
    case _ h3 =>
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, e]
    split
    case _ h5 =>
      simp at h3;
      split
      apply ih h1 h2
      split
      case _ => apply ih h1 h2
      case _ i h5 _ _ _ h6 =>
        exfalso;
        simp [List.findIdx?_eq_some_iff_getElem] at h5; rcases h5 with ⟨hi, h5, h7⟩; simp at h6;
        rcases h6 with ⟨w, y, h7, h8, h9, h10⟩; subst h9; simp [List.getElem?_eq_getElem hi] at h8;
        replace h3 := h3 y h7; apply h3; grind
    case _ h5 =>
      split
      case _ i _ _ _ h6 =>
        exfalso;
        simp at h6; rcases h6 with ⟨w, h6, h7, h8, h9⟩; subst h8; simp at h5;
        simp [List.findIdx?_eq_some_iff_getElem] at h5; rcases h5 with ⟨hi, h5, h10⟩;
        simp [List.getElem?_eq_getElem hi] at h7; simp [h7] at h5; subst h5; replace h4 := h4 h6;
        apply h4; grind
      case _ h6 => apply ih h1 h2

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
    rcases h5 with ⟨scs, h5, h6⟩;
    cases h6
    have e : (x = iname) = False := by grind
    simp [Intermediate.lookup, e]
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
    simp[Vec.foldr_or_val_eq_none] at h2
    rcases h2 with ⟨h2, h3⟩;
    simp [Intermediate.lookup];
    split
    case _ e => subst e; contradiction
    simp [Vec.foldr_or_val_eq_none]
    apply And.intro
    apply ih h1 h2
    case _ ctors _ h4 h5 =>
      intro v v_in_vs
      replace v_in_vs := Vec.getElem_of_mem v_in_vs; rcases v_in_vs with ⟨i, v_in_vs⟩
      generalize zdef : Vec.map (fun x_1 => if x = x_1.1.fst then some (Surface.Entry.ctor x_1.1.fst x_1.snd x_1.1.snd) else none)
          ctors.zipIdx = z at *
      simp at v_in_vs; split at v_in_vs
      · case _ e =>
        subst v; exfalso;
        have lem : z[i] = z[i] := by rfl
        conv at lem =>
          lhs
          rw[<-zdef]
        simp [e] at lem; replace h3 := h3 z[i] (by simp [Vec.getElem_mem]); rw[h3] at lem; simp at lem
      · symm; apply v_in_vs

  case _ s _ _ _ ih => -- defn
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    cases h3;
    simp [Intermediate.lookup]; split
    case _ e => subst e; simp at h2
    have e : (x = s) = False := by grind
    simp [e] at h2
    apply ih h1 h2

  case _ s _ scs mτs _ ih => -- odata
    simp [bind, Except.bind_eq_ok_iff] at h1; rcases h1 with ⟨Γ', h1, h3⟩
    split at h3 <;> try simp at *
    rcases h3 with ⟨h3, _⟩
    cases h3
    split at h2 <;> try simp at h2
    have e : (x = s) = False := by grind
    simp [Intermediate.lookup, e]
    split at h2 <;> try simp at h2
    case _ h3 =>
      simp at h3;  rcases h3 with ⟨spTy, h3⟩; exfalso; apply h2 x spTy h3 rfl
    case _ h3 =>
      split at h2
      case _ h4 =>
        simp at h4 h2;
        rcases h4 with ⟨z, b, h4⟩
        exfalso; apply h2 x z b h4 rfl
      case _ h4 =>

        split
        case _ h5 =>
          simp at h5
          split
          case _ h6 =>
            simp at h6; apply ih h1 h2
          case _ h6 =>
            simp at h6;
            split
            case _ h7 =>
              simp [List.findIdx?_eq_some_iff_getElem] at h6;
              rcases h6 with ⟨hi, h6, h8⟩; simp at h7; apply ih h1 h2
            case _ i _ y spTy h7 =>
              exfalso; simp at h4; simp at h7;
              rcases h7 with ⟨y', z, tys, h8, h9, h10⟩; subst h9
              simp [List.findIdx?_eq_some_iff_getElem] at h6; rcases h6 with ⟨hi, h6, h9⟩
              simp [<-List.getElem_eq_iff (h := hi)] at h8; simp [h8] at h6; subst h6
              apply h4 z tys; grind
        case _ h5 =>
          split
          case _ h6 =>
            exfalso; simp [List.findIdx?_eq_some_iff_getElem] at h6 h5 h3;
            rcases h6 with ⟨y, h6, h7, h8, h9⟩; subst h8
            rcases h5 with ⟨hi, h5, _⟩
            simp [<-List.getElem_eq_iff (h := hi)] at h7; simp [h7] at h5; subst h5
            apply h3 h6; grind
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
    rcases h5 with ⟨scs', h5, h6⟩
    cases h6;
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
    case _ val => simp at val; simp [val]

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
    have lem := lookup_SI_data h h2; simp [lem,Intermediate.Entry.is_data]
  · simp [Intermediate.is_data, Option.getD_eq_iff];
    have lem := Surface.lookup_name_agrees h2; simp [Surface.Entry.name] at lem; subst x
    have lem := lookup_SI_odata h h2; rcases lem with ⟨_, _, lem⟩;
    simp [lem, Intermediate.Entry.is_data]


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

  case _ kc s Ks scs mτs Γ ih =>  -- class decl
    cases wf; case _ wftl wfhd =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h2⟩
    split at h2 <;> try simp at h2;
    case _ h3 =>
    rcases h2 with ⟨h2, h4⟩; subst G'
    cases wfhd; case _ c1 c2 c3 c4 c5 c6 =>
    constructor
    · apply Intermediate.GlobalWf.classDecl
      · apply h3
      · { intro i j hi hj ne; simp; apply c3 i j (by grind) (by grind) ne }
      · { intro i j hi hj ne; simp; apply c1 i j (by grind) (by grind) ne }
      · { intro i j hi hj ne; simp at ne; apply c6 i j (by grind) (by grind) ne }
      · { intro i mn τ hi h1; have h : i < mτs.length := by grind
          replace c4 := c4 i (mτs[i]).1 (mτs[i]).2 h; simp at h1;
          simp at c4; rcases h1 with ⟨e1, e2⟩; subst e1; subst e2;
          have lem1 : ⊢ ((Surface.Global.classDecl s Ks [] []) :: Γ) := by
            constructor
            · constructor
              assumption
              simp
              simp
              simp
              simp
              simp
              simp
            · apply wftl
          have lem2 : ⟦(Surface.Global.classDecl s Ks [] [] :: Γ)⟧ = .ok (Intermediate.Global.classDecl { name := s, kcU := kc, kind := Ks, fds := [], scs := [], mths := [] } :: Γ') := by
            simp [translate_SI, bind, Except.bind_eq_ok_iff]; exists Γ'; apply And.intro; apply h1
            simp [h3, pure, Except.pure]; simp [check_oms]
          generalize zdef : (mτs[i]).2 = z at *
          rcases z with ⟨k1, Ks1, k2, Ks2, k3, Ts, R⟩
          cases c4; case _ Δ _ p1 p2 p3 p4 =>
          replace c5 := c5 i mτs[i].1 R h; rcases c5 with ⟨c5a, c5b, c5c⟩
          rw[c5a] at zdef; cases zdef; simp at p1; subst Δ
          apply spine_kinding_SI_transfer (test := λ _ => true)
          apply lem2
          simp
          apply Surface.SpineKinding.valid
          rfl;
          · simp
          · simp; apply c5c.2.weaken_global lem1
          rfl
          · simp [Surface.Ty.data?, Core.Ty.mkApps_nats_spine, Surface.is_data, Surface.lookup, Surface.Entry.is_data]
        }
      · intro i mn R T tys hi tsp tys_shape; simp;
        replace c5 := c5 i mn R (by grind);
        rcases c5 with ⟨c5a, c5b, c5c, c5d⟩;
        apply And.intro
        · simp [mk_method_om]; subst tys; rw[c5a]; simp; symm;
          apply Core.Ty.mkApps_nats_spine_eta; apply tsp
        · apply And.intro; apply c5b; apply And.intro
          apply translate_SI_lookup_none h1 c5c
          apply kinding_SI_transfer h1 c5d
      · generalize zdef : List.map (fun x => (x.fst, Surface.mk_superclass_om s Ks x.2.fst x.2.snd)) scs = z at *
        intro i mn R T tys supCls tys2 hi T_spine e1 R_shape; simp;
        have lem : z[i] = z[i] := by rfl
        conv at lem =>
          rhs
          simp only [<-zdef]
        simp at lem;
        have hi : i < scs.length := by grind
        generalize qdef : Surface.mk_superclass_om s Ks supCls tys2 = q at *
        replace qdef := mk_superclass_om_shape qdef
        rcases q with ⟨qna, qKs1, qnb, qKs2, qnc, qAs, qR⟩
        simp at qdef;
        rcases qdef with ⟨e1, qdef⟩; subst e1; simp at qdef; rcases qdef with ⟨e1, e2, e3, qdef⟩
        subst e1; subst e2; subst e3; simp at qdef; cases qKs2; rcases qdef with ⟨e1, qdef⟩; subst e1;
        subst qdef;
        replace c2 := c2 i mn supCls tys2 hi
        apply And.intro
        · rw[lem]; simp; rcases c2 with ⟨e1', e2, e3⟩; apply And.intro;
          rw[e1'];
          rw[e1']; rw[e1'] at lem; simp at lem; simp;
          simp [Surface.mk_superclass_om]
          apply And.intro;
          · simp [e1] at T_spine; have lem := Core.Ty.mkApps_nats_spine_eta (T := T) (s := s) (tys := (List.range kc).reverse)
            simp at lem; replace lem := lem T_spine; symm; apply lem
          · have lem := Core.Ty.mkApps_nats_spine_eta (T := R) (s := supCls) (tys := tys2) R_shape
            symm; apply lem
        · rcases c2 with ⟨c2a, c2b, c2c, c2d, c2e⟩;
          apply And.intro
          apply c2b; apply And.intro; apply translate_SI_lookup_none h1 c2c;
          apply lookup_is_data_SI_some h1 c2d
    · apply ih wftl h1

  case _ iname _ _ _ _ _ _ _ _ _ ih => -- instance
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h1, h⟩
    split at h <;> try simp [Except.bind] at h
    split at h <;> try simp at h
    case _ h1 =>
    split at h <;> try simp at h
    case _ h2 =>
    split at h <;> try simp at h
    case _ e =>
    rcases e with ⟨e1, e2⟩; subst e1;
    split at h <;> try simp at h
    case _ mths h3 =>
    split at h <;> try simp at h
    case _ scs' h4 =>
    split at h <;> try simp at h
    subst G'
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ cls_name _ K i scs mτs h9 lks _ q1 e h5 =>
    simp [Option.toTM_some_eq_ok_iff, Core.Ty.mkApps_nats_spine] at h1;
    subst h1
    constructor
    · constructor
      · assumption
      · apply h2
      · have lem := spine_kinding_SI_transfer (test' := Intermediate.Ty.data? Core.DataConst.opn Γ') h1
                      (by intro T h; apply Ty.data?_SI_transfer h1 T h) q1
        apply lem
      · intro i hi;
        have lem3 := mk_inst_mths_SI_length h3; rcases lem3 with ⟨l1, l2⟩
        have lem := mk_inst_mths_SI_shape (by grind) h3
        have lem2 := mk_inst_mths_SI_indexing h3 i (by grind)
        rcases lem2 with ⟨lem2, lem3⟩
        have l3 : i < mτs.length := by grind
        grind
      · intro i hi;
        simp at h4; have lem1 := mk_inst_scs_SI_length h4
        have lem2 :=  mk_inst_scs_SI_shape h4 i lem1 (by grind)
        apply lem2
      · have lem3 := mk_inst_mths_SI_length h3; rcases lem3 with ⟨l1, l2⟩; grind
      · simp at h4; have lem1 := mk_inst_scs_SI_length h4; apply lem1
    · apply ih wftl h1



set_option maxHeartbeats 7000000
theorem translate_SI_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  Ω G'
:= by
  intro h
  have wf' := translate_SI_wf_sound wf h
  intro mn na nb nc Ks1 Ks2 Ts R qs _ _ h1 h2
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
      replace h1 := Vec.foldr_or h1
      cases h1
      case _ h1 => rcases h1 with ⟨i, h1⟩; simp at h1
      case _ h1 =>
        replace h2 := Intermediate.Query.opn_strengthen_ctor (by constructor; apply wfhd'; apply wftl') h2
        replace ih := @ih _ wftl h3 wftl' mn h1.2 h2
        rcases ih with ⟨i, n, cls, k1, k2, k3, Ks1, Ks2, tys, fds, scs, mths, ih⟩
        exists i + 1; exists n; exists cls; exists k1; exists k2; exists k3;
        exists Ks1; exists Ks2;
        exists tys; exists fds
        exists scs; exists mths
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
  case _ cls kc s Ks1 scs mτs _ ih => -- class Decl
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h3, h⟩
    split at h <;> simp at *
    rcases h with ⟨h, h4⟩
    subst G'
    replace h2 := Intermediate.Query.opn_strengthen_class wf' h2
    cases wf; case _ wftl wfhd =>
    cases wf'; case _ wftl' wfhd' =>
    cases wfhd'; case _ ci1 ci2 ci3 ci4 ci5 ci6 =>
    cases wfhd; case _ cs1 cs2 cs3 cs4 cs5 cs6 =>
    simp [Intermediate.lookup] at h1
    split at h1 <;> try simp at h1
    have ne1 : (mn = s) = False := by grind
    split at h1 <;> try simp at h1
    case _ h5 =>
      split at h1 <;> try simp at h1
      case _ h6 =>
        replace ih := ih wftl h3 wftl' h1 h2; rcases ih with ⟨i, ih⟩; exists i+1
      case _ i h6 =>
        split at h1 <;> try simp at h1
        · replace ih := ih wftl h3 wftl' h1 h2; rcases ih with ⟨i, ih⟩; exists i+1;
        case _ spTy h7 =>
          rcases h1 with ⟨e1, e2, e3⟩; subst e1; subst e2;
          simp [List.findIdx?_eq_some_iff_getElem] at h6
          rcases h6 with ⟨j, hj, lk⟩; subst hj;
          rcases spTy with ⟨na, Ks1, nb, Ks2, nc, As, R⟩; cases e3
          let T := (Core.Ty.mkApps_nats (gt#s) ((List.range kc)).reverse)
          let tys := ((List.range kc).map (t#·)).reverse
          -- The point here is that Ts = #(T) and T is the class
          -- replace ci2 := ci2 i (scs[i].1) R T tys (by grind) (by simp[T, tys, Core.Ty.mkApps_nats_spine]) (by simp [tys])
          -- rcases ci2 with ⟨e1, e2⟩; simp at e1 e2; replace e1 := mk_superclass_om_shape e1;
          -- simp at e1; rcases e1 with ⟨e1, e2⟩; subst T; subst R; simp at h7;
          -- rcases h7 with ⟨a, b, h7, h8, h9, h10⟩; replace h10 := mk_superclass_om_shape h10;
          -- simp at h10; rcases h10 with ⟨e1, h10⟩; subst e1; simp at h10; rcases h10 with ⟨e1, e2, e3, e4, h10⟩
          -- subst e1; subst nb; subst nc; simp at e4; subst e4
          -- cases qs; cases h2; case _ h2 _ =>
          -- simp [Intermediate.lookup_ctor?, Core.Ty.mkApps_nats_spine] at h2;
          -- simp [Option.getD_eq_iff] at h2;
          -- rcases h2 with ⟨ent, h3, h4⟩;
          -- exfalso; apply Intermediate.lookup_none_ctor? wftl' _ h3 h4
          -- assumption
          sorry


    case _ i h5 =>
      -- The point here is that Ts = #(T) and T is the class
      simp [List.findIdx?_eq_some_iff_getElem] at h5;
      rcases h5 with ⟨hi, h5, h6⟩
      split at h1 <;> try simp at h1
      case _ spTy h7 =>
        clear ih
        rcases h1 with ⟨e1, e2, e3⟩; subst e1; subst e2;
        simp at h7; simp at *
        replace cs5 := cs5 i (mτs[i].1) R (by grind); rcases cs5 with ⟨e1, e2⟩
        let T := (Core.Ty.mkApps_nats (gt#s) ((List.range kc)).reverse)
        let tys := ((List.range kc).map (t#·)).reverse
        sorry
        -- let R :=
        -- replace ci5 := ci5 i (mτs[i].1) R T tys (by grind) (by simp[T, tys, Core.Ty.mkApps_nats_spine]) (by simp [tys])
        -- simp at ci5; rw[e1] at ci5; simp at ci5; rcases ci5 with ⟨e3, e4⟩
        -- unfold mk_method_om at e3; simp at e3;
        -- rcases h7 with ⟨x, b, h7, h8, h9⟩; simp [mk_method_om] at h9;
        -- cases h9; simp at e3;
        -- simp [List.getElem?_eq_some_iff] at h7; rcases h7 with ⟨hi, h7⟩; rw[e1] at h7; simp at h7; rcases h7 with ⟨_, h7⟩
        -- subst h7; simp at e3; rcases e3 with ⟨e1, e3⟩; subst e1; simp at e3; rcases e3 with ⟨e1, e2, e3⟩; subst e1; subst e2
        -- simp at e3; rcases e3 with ⟨e1, e2, e3⟩; subst e1; subst e2; simp at e3; subst e3;
        -- subst h8; subst h5; subst T;
        -- cases qs; cases h2; case _ h2 _ =>
        -- simp [Intermediate.lookup_ctor?, Core.Ty.mkApps_nats_spine] at h2;
        -- simp [Option.getD_eq_iff] at h2;
        -- rcases h2 with ⟨ent, h3, h4⟩;
        -- exfalso; apply Intermediate.lookup_none_ctor? wftl' _ h3 h4
        -- assumption
      · replace ih := ih wftl h3 wftl' h1 h2; rcases ih with ⟨i, ih⟩; exists i+1
  case _ cls1 iname na' Ks1' nb' Ks2' nc' As' R' ts _ ih => -- inst
    cases wf; case _ wftl wfhd =>
    cases wfhd; case _ lks q1 q2 q3 q4 =>
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨Γ', h, h3⟩
    split at h3
    · simp [Option.toTM] at h3
      · split at h3 <;> simp [Except.bind_eq_ok_iff] at h3;
        case _ cls_name k1' _ _ _ mτs k2' _ _ _ _ rsp =>
        rcases h3 with ⟨cls, ⟨tys, h3⟩, h4⟩
        repeat (split at h4 <;> try simp [Except.bind_eq_ok_iff] at h4)
        case _ k1 _ _ _ _ e =>
        rcases e with ⟨e1, e'⟩; subst e1; cases h3;
        rcases h4 with ⟨mths', h4, h5⟩
        rcases h5 with ⟨scs', h5, h6⟩
        have lem := Core.Ty.mkApps_nats_spine cls_name (List.range k2').reverse
        rw[lem] at rsp; cases rsp
        have ts_len := mk_inst_mths_SI_length h4; rcases ts_len with ⟨_, ts_len⟩
        simp [e', ts_len] at h6; subst G'
        cases wf'; case _ wftl' wfhd' =>
        cases wfhd'; case _ e _ K' _ lki1 _ _ lki2 _ _ _ =>

        sorry
        -- cases wf'; case _ wftl' wfhd' =>
        -- cases wfhd'; case _ _ _ _ e _ K' _ lki1 _ _ _ _ _ lki2 _ _ _ =>
        -- -- cases q1;
        -- rw[lki2] at lki1; cases lki1;
        -- simp [Intermediate.lookup] at h1
        -- split at h1
        -- simp at h1

        -- have lem := Intermediate.lookup_openm_shape wftl' h1
        -- rcases lem with ⟨na, Ks1, T, R, tys, e⟩
        -- simp at e; rcases e with ⟨⟨e1, e2⟩, e3⟩; subst e1; simp at e2; rcases e2 with ⟨e2a, e2b, e2⟩;
        -- subst e2a; subst e2b; simp at e2; rcases e2 with ⟨e2a, e2b, e2⟩; subst e2a; subst e2b; simp at e2;
        -- rcases e2 with ⟨e2a, e2b⟩; subst e2a; subst e2b;
        -- cases qs; case _ q qs =>
        -- cases qs
        -- cases decEq q iname
        -- case _ e =>
        --   -- q ≠ iname
        --   cases decEq cls1 cls_name
        --   case _ e' =>
        --     replace e' : cls_name ≠ cls1 := by grind
        --     replace e : q ≠ iname := by grind
        --     have lem1 := Intermediate.Query.strength_inst1 h2 e3 e
        --     replace ih := ih wftl h wftl' h1 lem1
        --     rcases ih with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, As, fds, scs, mths, ih⟩
        --     exists i + 1; exists n; exists cls_name; exists k1; exists k2; exists k3; exists Ks1; exists Ks2
        --     exists As; exists fds; exists scs; exists mths
        --   case _ e' => -- cls = cls2
        --     subst e'
        --     replace e : q ≠ iname := by grind
        --     have lem1 := Intermediate.Query.strength_inst1 h2 e3 e
        --     replace ih := ih wftl h wftl' h1 lem1
        --     rcases ih with ⟨i, n, cls_name, k1, k2, k3, Ks1, Ks2, As, fds, scs, mths, ih⟩
        --     exists i + 1; exists n; exists cls_name; exists k1; exists k2; exists k3; exists Ks1; exists Ks2
        --     exists As; exists fds; exists scs; exists mths
        -- case _ e => -- q = iname
        --   subst e
        --   cases decEq cls1 cls_name
        --   case _ e => -- cls1 ≠ cls_name
        --     exfalso
        --     cases h2; case _ h1 h2 =>
        --     simp [Intermediate.lookup_ctor?] at h1; rw[e3] at h1; split at h1 <;> simp at *
        --     simp [Intermediate.lookup, Intermediate.Entry.ctor?] at h1; case _ e =>
        --     rcases e with ⟨e1, e'⟩; subst e1; subst e'
        --     have lem := Core.Ty.mkApps_nats_spine cls_name ((List.range na').map (·+ nb')).reverse
        --     simp [lem] at h1; cases h1; contradiction
        --   case _ e => -- cls1 = cls_name
        --     subst e
        --     exists 0; exists q; exists cls1; exists na'; exists nb'; exists nc'; exists Ks1'; exists Ks2';
        --     exists As'; exists []; exists []; exists mths; simp
        --     have lem := mk_inst_mths_SI_shape (by grind) h4
        --     have lem1 := mk_inst_mths_SI_indexing h4
        --     have lem2 := Intermediate.lookup_openm_index wftl' h1 lki2
        --     rcases lem2 with ⟨j, hj, lem2⟩; subst lem2
        --     replace lem1 := lem1 j hj
        --     rcases lem1 with ⟨lem1a, lem1b⟩
        --     replace lem := lem mths[j] (by grind)
        --     rcases lem with ⟨mn', n, na, nb, v', t, lem⟩
        --     exists j; exists (mths[j]).2.2.2; rw[lem]; simp
        --     exists #((q, ⟨n, (v', na, nb)⟩));
        --     apply And.intro
        --     grind
        --     constructor; grind; simp; constructor
    · simp at h3

end Translation.SI

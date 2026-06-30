import LeanSubst
import Core.Reduction
import Core.Reduction.Definition
import Core.Eval.SmallStep

open Lilac

namespace Core

theorem Term.is_data_sound :
  Term.is_data dc s = some c ->
  Term.IsData dc s c
:= by
  intro h
  fun_induction Term.is_data <;> simp at *
  case _ =>
    subst h; apply Term.IsData.nil
  case _ ih =>
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
    simp at h; rcases h with ⟨h3, h4⟩
    subst c; subst dc
    replace ih := ih h2
    apply Term.IsData.cons
    apply ih
    simp; apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · apply And.intro
        · rfl
        · apply And.intro
          · rfl
          · apply And.intro
            · rfl
            · apply And.intro
              · rfl
              · rfl
    rfl


theorem check_instance_eq_sound :
  check_instance_eq m n x y ctors p = true ->
  m = n ∧ x = y := by
intro h
unfold check_instance_eq at h
simp at h; rcases h with ⟨e , h⟩
apply And.intro e.2 e.1

theorem pattern_match_sound {m : Nat} {cs : Vec Constructor m} {ps : Pattern m} :
  pattern_match cs ps = true ->
  Pattern.Match cs ps
:= by
intro h
fun_induction pattern_match <;> simp at *
apply Pattern.Match.nil
· case _ ih =>
  rcases h with ⟨⟨⟨⟨h, e⟩, e1⟩, e2⟩, e3⟩
  subst e; subst e1; subst e2; subst e3
  replace ih := ih h
  apply Pattern.Match.cons ih rfl rfl


theorem get_instance_sound {G : List Global} :
   get_instance x cs G = some ⟨i, _, p, t⟩ ->
   G[i]? = some (Global.inst x p t)
:= by
intro h
unfold get_instance at h; simp at h
generalize fdef : get_instance_from_idx x cs G = f at *
generalize odef : instance_idx? x cs G = o at *
cases o <;> simp at *
case _ i =>
unfold instance_idx? at odef;
rw[List.findIdx?_eq_some_iff_getElem] at odef;
rcases odef with ⟨i_le, odef1, odef2⟩
split at odef1
case _ g n y p a e =>
  unfold get_instance_from_idx at fdef;
  have lem := check_instance_eq_sound odef1
  rcases lem with ⟨e1, e2⟩; subst e1; subst e2
  simp at fdef; rw[<-fdef] at h; simp at h;
  rw[List.getElem_eq_iff] at e;
  rw[e] at h; simp at h;
  rcases h with ⟨h1, h2⟩
  clear odef1
  rcases h2 with ⟨e1, e2, e3, e4⟩
  subst e2; subst e3; simp at e4; rcases e4 with ⟨e4, e5⟩
  subst e4; subst e5; apply e
· cases odef1


theorem get_match_sound {ctors : Vec Constructor m} {ps : Vec (Pattern m) n}:
  get_match ctors ps = some i ->
  Pattern.Match ctors (ps[i])
 := by
 intro h
 unfold get_match at h
 replace h := Vec.findIdx_sound h
 replace h := pattern_match_sound h
 simp at h; apply h

theorem eval_sound (Γ : GlobalEnv) :
  M.eval Γ = some N ->
  Γ ⊢ M ~> N := by
intro h
fun_induction Term.eval generalizing N <;> simp at h
case _ =>  -- lookup defn
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  cases h;
  apply Red.defn h2
case _ ih => -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨i, m, p, t⟩, h4, h⟩
  simp at h; rcases h with ⟨⟨e1, h5⟩, h⟩
  subst e1;
  replace h2 := Term.is_data_sound h2
  replace h4 := get_instance_sound h4
  replace h5 := pattern_match_sound (cs := h1) (ps := p) h5
  simp at h5
  apply Red.openm_match (i := i) (b := t) (b' := N)
  · apply h2
  · apply h4
  · apply h5
  · simp; symm at h; apply h

case _ ss _ i j ih1 ih2 => -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; rcases h with ⟨h3, h4⟩

  replace j := Vec.findIdx_sound j
  rw[Option.isSome_iff_exists] at j; rcases j with ⟨t', j⟩
  rw[h3] at j; simp at j; subst h1
  replace ih2 := ih2 h2
  replace ih1 := ih1 i h2
  subst N
  apply Red.openm_congr i
  · have e1 := Vec.to_get_elem (ss.to.set i t') i
    have e2 := Vec.get_set_eq (a := t') (v := ss.to) (i := i)
    rw[e1, e2]; apply ih1
  · intro j h;
    replace h : i ≠ j := by grind
    have lem := Vec.get_set_neq h (a := t') (v := ss.to)
    symm at lem
    simp [<-Vec.to_get_elem] at lem; apply lem


case _ ih => -- mtch
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i, h4, h⟩
  simp at h; symm at h
  replace h2 := Term.is_data_sound h2
  replace h4 := get_match_sound h4; rw[<-Fun.Vec.to_get_elem] at h4
  apply Red.data_match (i := i)
  · apply h2
  · apply h4
  · apply h

case _ ss _ _ m_ss i j ih1 ih2 => -- mtch congr
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; subst h
  replace ih2 := ih2 h2
  apply Red.match_congr
  · have e1 := Vec.to_get_elem (ss.to.set i h1) i;
    have e2 := Vec.get_set_eq (a := h1) (v := ss.to) (i := i)
    rw[e1, e2]; apply ih2
  · intro j h;
    replace h : i ≠ j := by grind
    have lem := Vec.get_set_neq h (a := h1) (v := ss.to)
    symm at lem; simp [<-Vec.to_get_elem] at lem; apply lem


case _ => -- Λ[K] t •[T]
  subst N; constructor

case _ ih => -- t •[T]
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; subst N
  constructor; apply ih h2

case _ => -- prj 0 app
  subst N; apply Red.prj_fst_app

case _ => -- prj0 ->
  subst N; apply Red.prj_fst_arr

case _ => -- prj 1 app
  subst h
  apply Red.prj_snd_app

case _ => -- prj 1 arrow
  subst h
  apply Red.prj_snd_arr

case _ ih => -- prj congr
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨t', h1, h⟩
  simp at h; subst N
  replace ih := ih h1
  apply Red.ctor1_congr ih

case _ => -- β
  subst N
  apply Red.beta

case _ ih1 => -- t1 • t2 ~> t1' • t2
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨t', h2, h⟩
  simp at h; subst N
  replace ih1 := ih1 h2
  apply Red.app_congr ih1

case _ => -- ∀c[refl] •c[refl]
  subst h; apply Red.apptc

case _ ih =>
  subst N
  apply Red.apptc_congr2;
  apply ih; assumption

case _ ih =>
  subst h;
  apply Red.apptc_congr1
  apply ih; assumption


case _ => -- t ▸ refl A ~> t
  subst h
  constructor

case _ ih =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; subst N
  apply Red.cast_congr; apply ih h2

end Core

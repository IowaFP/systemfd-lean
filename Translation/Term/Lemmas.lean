import Common.Vec
import Core.Ty
import Core.Term
import Core.Metatheory
import Surface.Ty
import Surface.Term

import Translation.Ty
import Translation.Term

import Translation.Ty.Lemmas

import Translation.Ty
import Translation.Term
import Translation.Global
import Core.Typing
import Core.Metatheory.Inversion
import Core.Metatheory.Global


import Surface.Typing
import Core.Typing

open LeanSubst
open Lilac

namespace Translation

theorem Vec.traverse_eq_pure_iff_getElem_TM {α β n v2} {f : α -> TM β} :
  {v1 : Vec α n} ->
  v1.traverse f = Except.ok v2 ->
  ∀ i : Fin n, f v1[i] = .ok (v2[i])
| .nil, h, i => Fin.elim0 i
| .cons x xs, h, i => by
  cases v2; case _ y ys =>
  simp at h; unfold Seq.seq at h
  unfold Applicative.toSeq at h
  unfold Except.instMonad at h
  simp at h;
  simp [Except.bind_eq_ok_iff] at h
  rcases h with ⟨f, h, h1⟩
  simp [Functor.map, Except.map_eq_ok_iff] at h;
  simp [Except.map_eq_ok_iff] at h1
  rcases h with ⟨b, ha, hb⟩
  subst f; rcases h1 with ⟨v', h1, h2⟩
  simp at h2; rcases h2 with ⟨e1, e2⟩; subst e1; subst e2
  cases i using Fin.cases
  simp; apply ha
  simp; simp [Vec.traverse_eq_pure_iff_getElem_TM h1]

theorem Vec.map_seq_sound_TM {vs : Vec α n} {vs' : Vec β n} (f : α -> TM β) :
  (Vec.map f vs).sequence = .ok vs' ->
  ∀ i : Fin n, f (vs[i]) = .ok (vs'[i])
:= by
  intro h
  simp at h; apply traverse_eq_pure_iff_getElem_TM h


theorem synth_coercion_sound {G : Core.GlobalEnv} :
  Core.Ty.synth_coercion G Δ Γ A B = some t ->
  ∃ K, G&Δ, Γ ⊢ t : (A ~[K]~ B) ∧ G&Δ ⊢ A : K ∧ G&Δ ⊢ B : K
:= by
  intro h
  unfold Core.Ty.synth_coercion at h
  split at h <;> try simp at h
  case _ K _ j1 j2 =>
  rcases h with ⟨e, h⟩
  subst e; exists K
  replace h := Core.Synth.synth_coercion_term_sound h
  replace j1 := Core.infer_kind_sound j1
  replace j2 := Core.infer_kind_sound j2
  apply And.intro h
  apply And.intro j1 j2

theorem synth_term_sound {G : Core.GlobalEnv} {j : G&Δ, Γ ⊢ t : τ}:
  Core.Ty.synth_term G Δ Γ τ = .ok ⟨t, j⟩ ->
  G&Δ, Γ ⊢ t : τ
:= by
  intro h;
  simp [Core.Ty.synth_term, bind, Except.bind_eq_ok_iff] at h;
  rcases h with ⟨⟨t, τ', j⟩, h2, h3⟩
  split at h3 <;> try simp at h3
  case _ h =>
  simp at h; subst h
  rcases h3 with ⟨e, h3⟩; simp at h; assumption


theorem lookup_openm_implies_lookup_spine_type {G : Core.GlobalEnv} :
  Core.lookup x G = some (.openm x ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  Core.lookup_spine_type .openm G x = some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩
:= by  intro h; simp [Core.lookup_spine_type, h, Core.Entry.spine_type]


theorem lookup_ctor_implies_lookup_spine_type {G : Core.GlobalEnv} :
  Core.lookup x G = some (.ctor x i ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  Core.lookup_spine_type (.data .cls) G x = some ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩
:= by  intro h; simp [Core.lookup_spine_type, h, Core.Entry.spine_type]


theorem lookup_openm_implies_scrutinees_open_type {G : Core.GlobalEnv} (wf : ⊢ G):
  Core.lookup x G = some (.openm x ⟨m1, Ks1, m2, Ks2, n, Ts, R⟩) ->
  (∀ (i : Fin n), Core.Ty.data? .opn G Ts[i])
:= by
  intro h
  replace h := Core.EntryWf.from_lookup wf h
  cases h; case _ h1 h =>
  cases h1; grind


theorem type_directed_translation_soundness {G : Core.GlobalEnv} (wf : ⊢ G) :
  Surface.Term.type_directed_translate G Δ Γ T t = .ok t' ->
  G&Δ, Γ ⊢ t' : T
:= by
  intro h
  fun_induction Surface.Term.type_directed_translate generalizing t' <;> simp at h
  case _ ki _ lk e => -- var
    cases h; simp at e; cases e; apply Core.Typing.var lk
    simp at ki; replace ki := Core.infer_kind_sound ki
    apply ki
  case _ A _ ki B lk e => -- var with coercion
    simp [Functor.map, Except.map_eq_ok_iff] at h; rcases h with ⟨t, h1, h2⟩
    simp [Option.toTM_some_eq_ok_iff] at h1
    replace h1 := synth_coercion_sound h1
    simp at ki; replace ki := Core.infer_kind_sound ki
    subst h2
    rcases h1 with ⟨K, h1, h2, h3⟩
    have e := Core.Kinding.unique ki h3; subst K
    apply Core.Typing.cast (K := ★) -- K = ★
    apply Core.Kinding.var; simp
    apply h1
    simp; apply Core.Typing.var; apply lk; apply h2
    simp


  case _ Δ Γ τ _ _ _ _ τU τE as _ _ _ _ _ _ _ Ts R lk ih => -- overloading/globals
    simp [bind, Except.bind_eq_ok_iff, Option.toTM_some_eq_ok_iff] at h; rcases h with ⟨KsU, h1, h2⟩
    rcases h2 with ⟨KsE, h, h3⟩
    rcases h3 with ⟨h3, h4⟩
    rcases h3 with ⟨c, h3, h5⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h5; rcases h5 with ⟨ιs, h5, h6⟩
    rcases h4 with ⟨e, h4⟩
    rcases e with ⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩; subst e1 e2 e3 e4;
    replace e7 := Core.infer_kind_sound e7
    simp [Vec.beq_iff_eq] at e5 e6; subst e5 e6
    generalize σdef1 : (List.map su τE.list).reverse ++ (List.map su τU.list).reverse ++ Subst.id Core.Ty = σ1 at *
    generalize σdef2 : (List.map su (τU ++ τE).list).reverse ++ Subst.id Core.Ty = σ2 at *
    have lemσ : σ1 = σ2 := by simp [<-σdef1, <-σdef2]
    generalize zdef : (Vec.from_list
        (List.map (fun x => Surface.Term.type_directed_translate G Δ Γ x.val.fst x.val.snd)
          (Ts[List.map su (τU ++ τE).list.reverse ++ Subst.id Core.Ty].list.zip (as.to).list).attach)) = z at *
    have lem1 := Vec.from_list_length zdef
    simp at lem1; subst lem1
    replace h3 := synth_coercion_sound h3
    replace lk' := Core.EntryWf.from_lookup wf lk; cases lk'; case _ lk2 lk' =>
    replace lk := lookup_ctor_implies_lookup_spine_type lk
    cases lk2; case _ Ks2 _ _ _ _ _ h9 h10 h11 h12 h13 =>
    subst t'
    rcases h3 with ⟨K, h3, e3, e4⟩
    replace e3 := Core.Kinding.unique e3 e7; subst e3
    apply Core.Typing.cast (A := R[σ1]) (K := ★) (B := τ)
    apply Core.Kinding.var (K := ★); simp;
    apply h3
    simp;
    apply Core.Typing.spctor (Ts := Ts) (Ts' := Ts[σ1]) (R := R) (R' := R[σ1]) (ts := ιs.to)
    · apply lk
    · simp [σdef1]
    · simp [σdef1]
    · intro i; replace h1 := Vec.traverse_eq_pure_iff_getElem_Option h1 i; replace h1 := Core.infer_kind_sound h1; apply h1
    · intro i; replace h := Vec.traverse_eq_pure_iff_getElem_Option h i; replace h := Core.infer_kind_sound h; apply h
    · intro i; simp [Vec.sequence] at h5; replace h3 := Vec.traverse_eq_pure_iff_getElem_TM h5 i;
      simp at h3; simp [<-Vec.get_to]
      rcases z with ⟨z_len, zs⟩
      simp at *
      apply  @ih _ (as i)
      · simp [<-σdef1];
        generalize ldef : Ts[List.map su (τU ++ τE).list.reverse ++ Subst.id Core.Ty].list.zip (as.to).list = l at *
        generalize kdef : List.map (fun x => Surface.Term.type_directed_translate G Δ Γ x.val.fst x.val.snd) l.attach = k at *
        simp [List.map_attach_eq_pmap] at kdef;
        have lem : l.length = z_len := by rw[<-ldef]; simp [List.length_zip]
        have lem2 : l[i] = l[i] := by rfl
        have lem3 : (Ts[List.map su (τU ++ τE).list.reverse ++ Subst.id Core.Ty].list.zip (as.to).list)[i]'(by grind) = l[i] := by grind
        simp at i; simp at lem3; simp at ldef; rw[ldef]; clear ih;
        simp [List.mem_iff_getElem]; exists i; simp [<-lem3]
        cases z_len;
        apply i.elim0
        simp [Vec.get_list_to_get, <-Vec.to_get_elem]; grind
      · clear ih; rw[<-h3]; simp at i; replace zdef := Vec.from_list_indexing2 zdef i; simp at zdef;
        simp[zdef, <-σdef1]; cases z_len
        apply i.elim0
        simp [Vec.get_list_to_get]; simp [<-Vec.to_get_elem]
    · simp [Core.lookup_ctor?]; simp [Core.Ty.is_data] at h13; split at h13 <;> try simp at h13;
      case _ h14 => simp [h14, lk', Core.Entry.ctor?]
    · simp; intro i hi; replace h4 := h4 i hi; simp [<-Core.Ty.FV.reflection] at h4; apply h4
    · simp
    simp


  case _ τ _ _ _ _ τU τE _ _ x _ Ks1 Ks2 nc Ts R lk => -- overloading openm
    simp [bind, Except.bind_eq_ok_iff, Option.toTM_some_eq_ok_iff] at h; rcases h with ⟨KsU, h1, h⟩
    split at h <;> try simp at h
    case _ ιs h3 =>
    rcases h with ⟨h, e⟩
    rcases h with ⟨h, h4⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h; rcases h with ⟨c, h⟩
    simp [Option.toTM_some_eq_ok_iff] at h; rcases h with ⟨h, e⟩; subst e
    replace h := synth_coercion_sound h
    rcases h with ⟨K, h7, h8, h9⟩;
    rcases e with ⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩; subst e1 e2 e3 e4; simp [Vec.beq_iff_eq] at e5;
    subst e5 e6;
    replace e7 := Core.infer_kind_sound e7;
    replace lk1 := lookup_openm_implies_lookup_spine_type lk
    replace lk' := Core.EntryWf.from_lookup wf lk; cases lk'; case _ lk2 lk' =>
    cases lk2; case _ Ks2 _ _ _ _ _ h9 h10 h11 h12 h13 =>
    generalize σdef : (List.map su τE.list).reverse ++ (List.map su τU.list).reverse ++ Subst.id Core.Ty = σ at *
    replace e7 := Core.Kinding.unique e7 h8; subst e7
    apply Core.Typing.cast (A := R[σ]) (B := τ)
    apply Core.Kinding.var; simp; rfl
    apply h7
    apply Core.Typing.spctor (v := .openm) (Ts := Ts) (Ts' := Ts[σ]) (R := R) (R' := R[σ]);
    · apply lk1
    · simp [σdef]
    · simp [σdef]
    · intro i; replace h1 := Vec.traverse_eq_pure_iff_getElem_Option h1 i; replace h1 := Core.infer_kind_sound h1; apply h1
    · intro i; apply i.elim0
    · intro i; replace h3 := Vec.traverse_eq_pure_iff_getElem_TM h3 i;
      generalize zdef : ιs[i] = ι at *;
      rcases ι with ⟨t, τ, j⟩
      simp [Vec.to_get_elem, zdef]; simp [<-h4]; rw [zdef]; simp; apply j
    · simp
    · simp
    · simp; replace lk := lookup_openm_implies_scrutinees_open_type wf lk'; apply lk
    simp

  case _ ih => -- lamt
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨t'', h1, h2⟩
    rcases h2 with ⟨e1, e2⟩; subst e2; cases e1
    replace ih := ih h1
    apply Core.Typing.lamt
    · replace ih := Core.terms_have_star_types wf ih; apply Core.Kinding.all; apply ih
    · apply ih
  case _ e _ _ ih => -- lam
    simp at e; replace e := Core.infer_kind_sound e
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨t'', h1, h2⟩
    replace ih := ih h1
    simp [Functor.map, Except.map_eq_ok_iff, Option.toTM_some_eq_ok_iff] at h2; rcases h2 with ⟨c, h2, h3⟩
    replace h2 := synth_coercion_sound h2; subst h3
    rcases h2 with ⟨K, h2, h4, h5⟩;
    have h2' := Core.terms_have_star_types wf h2
    cases h4; cases h5;
    apply Core.Typing.cast (K := ★); apply Core.Kinding.var; simp; apply h2; simp;
    · apply Core.Typing.lam
      · assumption
      · apply ih
    · simp

  case _ t1 t2 τ ih1 ih2 =>  -- app
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨t2', h1, h2⟩
    replace ih1 := ih1 h1
    simp [Functor.map, Except.map_eq_ok_iff] at h2; rcases h2 with ⟨t1', h2, h3⟩
    replace ih2 := ih2 h2
    subst t'
    apply Core.Typing.app ih2 ih1

  case _ t1 τ τ2 ih => -- appt
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨t', h, h3⟩
    split at h3 <;> try simp at h3
    case _ h4 =>
    split at h3 <;> try simp at h3
    rcases h3 with ⟨h3, h5⟩; subst h5
    rcases h3 with ⟨h3, h5⟩; cases h3;
    apply Core.Typing.appt
    apply ih h
    apply Core.infer_kind_sound h4
    apply h5

  case _ Δ Γ τ m n ss τs pats bs lk h1 ih1 ih2 =>  -- mtch
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨ss', h2, h3⟩
    simp [Functor.map, Except.map_eq_ok_iff] at h3; rcases h3 with ⟨ΔsΓs, h3, h4⟩
    rcases h4 with ⟨bs', h4, h5⟩
    subst t'
    cases m <;> (cases n; simp at *)
    simp at lk
    case _ m n =>
    simp at lk; simp [Option.isSome_iff_ne_none, Option.ne_none_iff_exists] at lk;
    rcases lk with ⟨⟨_, lk⟩, τs_ty⟩; symm at lk;
    apply Core.Typing.mtch (S := τs) (ss := ss'.to) (ps := pats) (ts := bs'.to) (ζ := (ΔsΓs.map (·.1)).to) (ξ := (ΔsΓs.map (·.2)).to)
    · intro i; apply ih1; simp [h1] at h2; replace h1 := Vec.traverse_eq_pure_iff_getElem_TM h2 i;
      simp at h1; simp [<-Vec.to_get_elem] at h1; apply h1
    · intro i;
      simp [<-Vec.get_to]; simp [Vec.all_eq_true] at τs_ty;
      replace τs_ty := τs_ty (Fun.Vec.to τs)[i] Vec.getElem_mem; apply τs_ty
    · intro i; replace h3 := Vec.traverse_eq_pure_iff_getElem_TM h3 i; simp at h3;
      simp [<-Vec.to_get_elem] at h3; simp [Option.toTM_some_eq_ok_iff] at h3;
      replace h2 := Core.pattern_binders_sound h3
      simp [<-Vec.get_to] at h2; simp [<-Vec.get_to]; apply h2
    · intro i; replace h3 := Vec.traverse_eq_pure_iff_getElem_TM h3 i; simp at h3;
      simp [<-Vec.to_get_elem] at h3; simp [Option.toTM_some_eq_ok_iff] at h3;
      replace h3 := Core.pattern_binders_sound h3
      simp [<-Vec.get_to]
      simp [<-Vec.get_to] at h4
      simp at ih2;
      replace ih2 := @ih2 ΔsΓs i (bs'.to i); simp [<-Vec.get_to] at ih2
      apply ih2; clear ih2
      generalize fdef : (λ i : Fin (n + 1) =>
        (Surface.Term.type_directed_translate G (ΔsΓs[i].fst ++ Δ) (ΔsΓs[i].snd ++ Γ⟨Ren.add Core.Ty ΔsΓs[i].fst.length⟩)
          τ⟨Ren.add Core.Ty ΔsΓs[i].fst.length⟩ (bs.to)[i])) = f at *
      have lem := Vec.map_seq_sound_TM (vs := Fun.Vec.to f) (vs' := bs') (f := λ x => x) (h4 |> cast (by simp)) i
      simp [<-fdef] at lem; simp [<-Vec.to_get_elem] at lem; simp [<-Vec.get_to] at lem;
      apply lem
    intro q h;
    have lem := Core.pattern_exhaustive_sound (ps := pats.to) wf h lk
    simp [Vec.get_to] at lem; apply lem

  case _ ih => -- annot
    simp [bind, Except.bind_eq_ok_iff] at h; rcases h with ⟨t'', h1, h2⟩
    simp [Functor.map, Except.map_eq_ok_iff, Option.toTM_some_eq_ok_iff] at h2; rcases h2 with ⟨c, h2, h3⟩
    replace h2 := synth_coercion_sound h2
    subst t'; replace ih := ih h1; rcases h2 with ⟨K, h2, h3, h4⟩
    have h1' := Core.terms_have_star_types wf ih
    have e := Core.Kinding.unique h3 h1'; subst e
    apply Core.Typing.cast (K := ★);
    · apply Core.Kinding.var; simp
    · apply h2
    · simp; apply ih
    · simp


#print axioms type_directed_translation_soundness

end Translation

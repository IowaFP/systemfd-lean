import Core.Ty
import Core.Term
import Core.Metatheory.Determined.Definition
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
import Core.Metatheory.SpineType
import Core.Term.Spine
import Surface.Typing
import Translation.Rename

open LeanSubst



theorem Translation.GlobalEnv.lookup_type_sound {G : Surface.GlobalEnv} : -- maybe generalize this to entry lookup?
  Surface.Global.Elab G G' ->
  (∀ (x : String) (T : Surface.Ty) (Δ : Core.KindEnv),
    (Surface.lookup_type G x = some T) ->
    ∃ T' b, (Core.lookup_type G' x = some T' ∧ T.translate = T' ∧ G'&Δ ⊢ T' : .base b)) := by
intro h1 i K Δ h2
sorry

theorem Translation.Entry.is_ctor_sound {G: Surface.GlobalEnv} :
  Surface.Global.Elab G G' ->
  Surface.is_ctor G x ->
  Core.is_ctor G' x := by sorry


theorem Translation.Term.Spine
  {t : Surface.Term} {t' : Core.Term} :
  t.spine = some (x, sp) ->
  t.translate G' Δ' Γ' = some t' ->
  ∃ sp', t'.spine = .some (x, sp') := by
intro h1 h5
induction t using Surface.Term.spine.induct generalizing x sp t' <;> simp [Surface.Term.spine] at *
case _ => exists []; rw[<-h5]; cases h1.1; cases h1.2; simp [Core.Term.spine]
case _ ih =>
  rw[Option.bind_eq_some_iff] at h5;
  rcases h5 with ⟨f', h5, h6⟩
  rw[Option.bind_eq_some_iff] at h6
  rcases h6 with ⟨a', h7, h8⟩
  cases h8
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨sp', h1, h8⟩
  cases h8
  replace ih := @ih sp'.1 sp'.2 f' h1 h5
  rcases ih with ⟨sp'', ih⟩
  simp [Core.Term.spine]
  exists (sp'' ++ [Core.SpineElem.term a']); rw[Option.bind_eq_some_iff]
  exists (sp'.fst , sp'')
case _ f a ih =>
  rw[Option.bind_eq_some_iff] at h5;
  rcases h5 with ⟨f', h5, h6⟩
  cases h6
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨sp', h1, h8⟩
  cases h8
  replace ih := @ih sp'.1 sp'.2 f' h1 h5
  rcases ih with ⟨sp'', ih⟩
  simp [Core.Term.spine]
  exists (sp'' ++ [Core.SpineElem.type a.translate]); rw[Option.bind_eq_some_iff]
  exists (sp'.fst , sp'')

theorem Translation.KindEnv.lift_sound  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv} {K : Surface.Kind} {K'}:
  Δ.translate = Δ' ->
  K.translate = K' ->
  Surface.KindEnv.translate (K::Δ) = K' :: Δ':= by
intro h1 h2
rw[Surface.KindEnv.translate, List.map_cons]
rw[Surface.KindEnv.translate] at h1
simp [h1, h2]

theorem Translation.TyEnv.lift_sound
  {G : Surface.GlobalEnv}
  {Δ : Surface.KindEnv}
  {Γ : Surface.TyEnv} {Γ' : Core.TyEnv}
  {A : Surface.Ty} {A' : Core.Ty} :
  Γ.translate = Γ' ->
  G&Δ ⊢s A : .base b ->
  A.translate = A' ->
  Surface.TyEnv.translate (A :: Γ) = (A'::Γ') := by
intro h1 j h2
simp [Surface.TyEnv.translate, Surface.TyEnv.map];
constructor
· assumption
· apply h1


theorem Translation.TyEnv.sound {Γ : Surface.TyEnv} {Γ' : Core.TyEnv} :
  Γ.translate = Γ' ->
  (∀ (i : Nat) (T : Surface.Ty),
     (Γ[i]? = some T) -> (Γ'[i]? = some T.translate)) := by
intro h1 i T h2;
induction Γ generalizing Γ' i <;> simp [Surface.TyEnv] at h2
case _ => cases h2
case _ hT Γ ih =>
  simp [Surface.TyEnv.translate] at *
  cases i <;> simp [Surface.TyEnv, Surface.inst_getElem?_TyEnv, Core.TyEnv, Core.inst_getElem?_TyEnv] at *
  case zero => subst h2; subst Γ'; simp[Surface.TyEnv.map];
  case succ n => subst Γ'; simp[Surface.TyEnv.map]; exists T;



theorem Translation.ValidTyHeadVariable.sound {G : Surface.GlobalEnv} :
  Surface.Global.Elab G G' ->
  T.translate = T' ->
  Surface.ValidTyHeadVariable T (Surface.is_data G) ->
  Core.ValidTyHeadVariable T' (Core.is_data G') := by
intro h1 h2 h3
induction h3
case _ sp h4 =>
rcases h4 with ⟨tnf, h4⟩
have lem := Translation.Ty.Spine tnf h2
rcases lem with ⟨sp', lem⟩
simp [Core.ValidTyHeadVariable]
exists (sp.fst)
apply And.intro
· exists sp'
· apply Translation.Entry.is_data_sound _ h4 h1


theorem Translation.StableTypeMatch.sound :
  Δ.translate = Δ' ->
  T.translate = T' ->
  R.translate = R' ->
  Surface.StableTypeMatch Δ T R ->
  Core.StableTypeMatch Δ' T' R' := by
intro h1 h2 h3 h4
induction h4 generalizing Δ' T' R' <;> try simp [Surface.Ty.translate] at *
case refl h =>
  rw[h3] at h2; cases h2
  have lem := Translation.Ty.Spine h h3
  rcases lem with ⟨sp, lem⟩
  apply Core.StableTypeMatch.refl lem
case arrow Δ B R A h ih =>
  cases h2
  apply Core.StableTypeMatch.arrow
  subst h1; subst R'; apply ih
case all K Δ B R a ih =>
  subst h2
  subst Δ'
  apply Core.StableTypeMatch.all
  simp [Surface.KindEnv.translate] at ih
  rw[Translation.Ty.Weaken h3] at ih
  apply ih


theorem Translation.PrefixTypeMatch.sound :
  Δ.translate = Δ' ->
  A.translate = A' ->
  T.translate = T' ->
  R.translate = R' ->
  Surface.PrefixTypeMatch Δ A T R ->
  Core.PrefixTypeMatch Δ' A' T' R' := by
intro h1 h3 h4 h5 h6
induction h6 generalizing Δ' A' T' R' <;> try simp [Surface.Ty.translate] at *
case refl B x Δ T j =>
  rw[h4] at h5; cases h5
  have lem := Translation.Ty.Spine j h3
  rcases lem with ⟨_, lem⟩
  apply Core.PrefixTypeMatch.refl
  assumption
case arrow Δ V B T A j1 ih =>
  subst A'; subst T'; subst R'
  apply Core.PrefixTypeMatch.arrow
  apply ih h1 rfl rfl rfl
case all K Δ B V T h ih =>
  subst A'; subst T'; subst Δ'; subst R'
  apply Core.PrefixTypeMatch.all
  apply ih
  rw[Surface.KindEnv.translate]; simp
  rfl
  rfl
  apply Translation.Ty.Weaken rfl


theorem Translation.ValidHeadVariable.sound
  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv}
  {Γ : Surface.TyEnv} {Γ' : Core.TyEnv}
  {t : Surface.Term} {t' : Core.Term}:
  Surface.Global.Elab G G' ->
  Δ.translate = Δ' ->
  Γ.translate = Γ' ->
  t.translate G' Δ' Γ' = some t' ->
  Surface.ValidHeadVariable t (Surface.is_ctor G) ->
  Core.ValidHeadVariable t' (Core.is_ctor G') := by
intro h1 h2 h3 h4 h5
induction h5
case _ sp h5 =>
rcases h5 with ⟨tnf, h5⟩
have lem := Translation.Term.Spine tnf h4
rcases lem with ⟨sp', lem⟩
simp [Core.ValidHeadVariable]
exists (sp.fst)
apply And.intro
· exists sp'
· apply Translation.Entry.is_ctor_sound h1 h5


theorem Translation.TyEnv.translation_comm_rename (Γ : Surface.TyEnv):
  Core.TyEnv.map (·[+1]) (Surface.TyEnv.map (Surface.Ty.translate) Γ) =
  Surface.TyEnv.map (Surface.Ty.translate) (Surface.TyEnv.map (·[+1]) Γ) := by
induction Γ <;> simp [Surface.TyEnv.map, Core.TyEnv.map] at *
case _ T tl ih =>
  apply And.intro
  · have lem := Translation.Ty.Weaken (T' := T.translate) rfl
    symm at lem; simp at lem; rw[lem];
  · apply ih


theorem quantifier_beast_lemma {Δ : Surface.KindEnv} {cs : Vect n Surface.Term} {CTy : Vect n Surface.Ty} :
(∀ (i : Fin n),
   ∃ t', Surface.Term.translate G' Δ.translate (Γ.map (fun x => x.translate)) (cs i) = some t' ∧
     t'.Determined ∧
     G'&Δ.translate,Surface.TyEnv.map (fun x => x.translate) Γ ⊢ t' : (CTy i).translate) ->
 (∃ t' : Vect n Core.Term,
    (∀ (i : Fin n),
       Surface.Term.translate G' Δ.translate (Γ.map (fun x => x.translate)) (cs i) = some (t' i)) ∧
    (∀ (i : Fin n), (t' i).Determined) ∧
    (∀ (i : Fin n), G'&Δ.translate,Surface.TyEnv.map (fun x => x.translate) Γ ⊢ (t' i) : (CTy i).translate)) := by
  intro h

  generalize vdef : Vect.seq (λ i => (cs i).translate G' Δ.translate (Γ.map (Surface.Ty.translate))) = v
  cases v
  case _ =>
    exfalso;
    unfold Vect.seq at vdef;
    generalize v'def : Vect.seq_lemma (fun i => Surface.Term.translate G' Δ.translate (Surface.TyEnv.map Surface.Ty.translate Γ) (cs i)) = v' at *
    cases v' <;> simp at *
    case _ v =>
      rcases v with ⟨x, v⟩
      replace h := h x
      rcases h with ⟨t', h1, h2, h3⟩
      rw[h1] at v; simp at v;
  case _ t' =>
    exists t';
    apply And.intro
    · apply Vect.seq_sound vdef
    · apply And.intro
      · intro i; replace h := h i; rcases h with ⟨t, h1, h2, h3⟩;
        have lem := Vect.seq_sound vdef i; rw[h1] at lem; cases lem; assumption
      · intro i; replace h := h i; rcases h with ⟨t, h1, h2, h3⟩;
        have lem := Vect.seq_sound vdef i; rw[h1] at lem; cases lem; assumption


@[simp]
abbrev Translation.SynthTermCompletenessLemmaType (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
  (i : SynthTermIdx) -> (SynthTermArgs i) -> Prop
| .one => λ (T, t) => t.Determined ∧ G&Δ, Γ ⊢ t : T
| .many => λ (ts , R , T) => Core.SpineType G Δ Γ ts R T ∧ ∀ t ∈ ts, t.Determined



theorem Translation.synth_term_completeness_lemma :
  Core.Translation.SynthTerm G Δ Γ m t ->
  Translation.SynthTermCompletenessLemmaType G Δ Γ m t := by
intro h
induction h <;> simp at *
case nil => apply Core.SpineType.refl
case rcons_o  i R T ηs η j iss inst ih h =>
  rcases ih with ⟨ih1, ih2⟩
  replace ih1 := Core.SpineType.oterm j h.2 ih1
  apply And.intro
  · assumption
  · intro t t_in_ηs
    cases t_in_ηs
    . grind
    . subst t; unfold Core.SpineElem.Determined; simp; exact h.1
case rcons_ty j1 j2 _ _ e ih1 ih2 =>
  apply And.intro
  · apply Core.SpineType.type j1 j2 e ih1.1
  · intro t h
    cases h
    case _ h => apply ih1.2 t h
    case _ h => subst h; unfold Core.SpineElem.Determined; simp
case var =>
  apply And.intro
  · constructor
  · assumption
case inst h1 h2 =>
  apply And.intro
  · apply Core.Term.Determined.spine h2.1 h1.2
  · apply Core.SpineType.apply h2.2 h1.1
case refl =>
  apply And.intro
  apply Core.Term.Determined.refl
  apply Core.Typing.refl; assumption
case sym ih =>
  apply And.intro
  · apply Core.Term.Determined.sym ih.1
  · apply Core.Typing.sym ih.2
case trans ih1 ih2 =>
  apply And.intro
  · apply Core.Term.Determined.trans; grind; grind
  · apply Core.Typing.seq; apply ih1.2; apply ih2.2
case fst ih =>
  apply And.intro
  · apply Core.Term.Determined.fst; grind
  · apply Core.Typing.fst _ _
    apply ih.2
    assumption
    assumption
case snd ih =>
  apply And.intro
  · apply Core.Term.Determined.snd; grind
  · apply Core.Typing.snd _ _
    apply ih.2
    assumption
    assumption
case capp ih1 ih2 =>
  apply And.intro
  · apply Core.Term.Determined.appc ih1.1 ih2.1
  · apply Core.Typing.appc ih1.2 ih2.2


theorem Translation.synth_term_completeness :
  Core.Translation.SynthTerm G Δ Γ .one (T ,  t) ->
  t.Determined ∧ G&Δ, Γ ⊢ t : T := by
intro h;
apply Translation.synth_term_completeness_lemma h


theorem Translation.Term.Spine2
  {t : Surface.Term} {t' : Core.Term} :
  Surface.Term.Elab G G' .inf Δ Γ t T t' ->
  t.spine = some (x, sp) ->
  ∃ sp', t'.spine = .some (x, sp') := by
intro h1 h2
generalize mdef : Mode.inf = m at *
induction h1 generalizing sp <;> simp [Surface.Term.spine, Core.Term.spine] at *
case global => apply h2.1
case app ηs _ a' is _ _ _ _ _ ih _ =>
  rw[Option.bind_eq_some_iff] at h2
  rcases h2 with ⟨fsp, h2, h3⟩
  simp at h3; rcases h3 with ⟨e1, h3⟩; subst e1
  replace ih := @ih fsp.snd h2
  rcases ih with ⟨f'sp, ih⟩
  have lem := Core.Spine.apply_eq ih
  rw[lem]; exists (f'sp ++ ηs ++ [Core.SpineElem.term a'])
  rw[Option.bind_eq_some_iff];
  exists (fsp.fst, f'sp ++ ηs)
  simp; rw[<-Core.Spine.apply_spine_compose]
  rw[Core.Spine.apply_eta]
case appt A _ _ _ _ _ ηs _ _ _ _ _ _ _ _ _ ih =>
  rw[Option.bind_eq_some_iff] at h2
  rcases h2 with ⟨fsp, h2, h3⟩
  simp at h3; rcases h3 with ⟨e1, h3⟩; subst e1
  replace ih := @ih fsp.snd h2
  rcases ih with ⟨f'sp, ih⟩
  have lem := Core.Spine.apply_eq ih
  rw[lem]; exists (f'sp ++ ηs ++ [Core.SpineElem.type A.translate])
  rw[Option.bind_eq_some_iff];
  exists (fsp.fst, f'sp ++ ηs)
  simp; rw[<-Core.Spine.apply_spine_compose]
  rw[Core.Spine.apply_eta]


theorem Translation.ValidHeadVariable.sound2
  {Δ : Surface.KindEnv} {Δ' : Core.KindEnv}
  {Γ : Surface.TyEnv}
  {t : Surface.Term} {t' : Core.Term}:
  Surface.Global.Elab G G' ->
  Δ.translate = Δ' ->
  Surface.Term.Elab G G' .inf Δ Γ t T t' ->
  Surface.ValidHeadVariable t (Surface.is_ctor G) ->
  Core.ValidHeadVariable t' (Core.is_ctor G') := by
intro h1 h2 h4 h5
induction h5
case _ sp h5 =>
rcases h5 with ⟨tnf, h5⟩
have lem := Translation.Term.Spine2 h4 tnf
rcases lem with ⟨sp', lem⟩
simp [Core.ValidHeadVariable]
exists (sp.fst)
apply And.intro
· exists sp'
· apply Translation.Entry.is_ctor_sound h1 h5


theorem Translation.Term.typing_spine
  {T : Surface.Ty} {C : Surface.Ty} {ηs : List Core.SpineElem} {G : Surface.GlobalEnv} {G' : Core.GlobalEnv}:
  Surface.Global.Elab G G' ->
  Surface.Ty.ImplicitSpineType G G' Δ Γ is ηs T C ->
  t.Determined ->
  G'&⟦Δ⟧,⟦Γ⟧ ⊢ t : T.translate ->
  (t.apply ηs).Determined ∧
  G'&⟦Δ⟧,⟦Γ⟧ ⊢ t.apply ηs : C.translate := by
intro h0 h1 h2 h3
induction h1 <;> simp [Core.Term.apply] at *
case nil => grind
case rcons_o o η os ηs T R j ηj _ ih =>
  replace ηj := Translation.synth_term_completeness ηj
  replace j := Translation.Ty.sound j h0 rfl
  rcases j with ⟨K, T', e1, e2, j⟩
  subst K; subst T'
  replace ih := ih h3
  rw[<-Core.Spine.apply_oterm]
  apply And.intro
  · apply Core.Term.Determined.app.1
    grind
  · apply Core.Typing.app (A := o.translate)
    apply j
    apply ih.2
    apply ηj.2

theorem Translation.Term.Sound
  {G : Surface.GlobalEnv}{G' : Core.GlobalEnv}
  {Δ : Surface.KindEnv} {Γ : Surface.TyEnv}
  {t : Surface.Term} {t' : Core.Term} {m : Mode}:
  Surface.Global.Elab G G' ->
  Surface.Term.Elab G G' m Δ Γ t T t' ->
  ∀ Δ' Γ',
  Δ.translate = Δ' ->
  Γ.translate = Γ' ->

  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T.translate

:= by
intro h2 h
induction h <;> simp at *
case var x T _ _ h j =>
     apply And.intro
     · apply Core.Term.Determined.var
     · apply Core.Typing.var
       apply Translation.TyEnv.sound rfl x T h
       have lem := Translation.Ty.sound j h2 rfl
       rcases lem with ⟨_, _, lem1, lem2, lem3⟩
       subst lem1; subst lem2; apply lem3

case global  x T Δ Γ B ηs is h1' j1 j2 =>
 let lem := Translation.GlobalEnv.lookup_type_sound h2 x T Δ.translate h1'
 rcases lem with ⟨T', _, lk, e1, _⟩; subst e1
 replace j1 := Translation.Ty.sound j1 h2 rfl
 rcases j1 with ⟨K, T', e1, e2, j1⟩; subst e1; subst e2
 have lem := Translation.Term.typing_spine h2 j2
   (Core.Term.Determined.global) (Core.Typing.global lk j1)
 apply lem

case app jk _ Cshape mists _ ih1 ih2 =>
  have lem := Translation.Term.typing_spine h2 mists ih1.1 ih1.2
  rcases lem with ⟨lem1, lem2⟩
  replace jk := Translation.Ty.sound jk h2 rfl
  rcases jk with ⟨K, T', e1, e2, jk⟩; subst e1; subst e2
  apply And.intro
  · apply Core.Term.Determined.app.1
    apply And.intro
    · apply lem1
    · apply ih2.1
  · subst Cshape
    apply Core.Typing.app
    apply jk
    apply lem2
    apply ih2.2

case appt A _ _ B _ _ _ _ _ _ _ jk e1 mists felab e2 ih =>
  have lem := Translation.Term.typing_spine h2 mists ih.1 ih.2
  rcases lem with ⟨lem1, lem2⟩
  replace jk := Translation.Ty.sound jk h2 rfl
  rcases jk with ⟨K, T', e1, e2, jk⟩; subst e1; subst e2
  have e3 := Translation.Ty.beta (a := A) (P := B) rfl rfl; simp at e3
  subst e2; rw[e3]; subst e1; simp at lem2
  apply And.intro
  · apply Core.Term.Determined.appt lem1
  · apply Core.Typing.appt
    apply lem2
    apply jk
    simp

case lam Δ A  Γ t B t' Ak _ ih =>
  apply And.intro
  · apply Core.Term.Determined.lam; apply ih.1
  · apply Core.Typing.lam
    · replace Ak := Translation.Ty.sound Ak h2 rfl;
      rcases Ak with ⟨_,_,e1,e2,Ak⟩; subst e1; subst e2
      apply Ak
    · apply ih.2

case lamt K Δ P t t' Γ jk _ ih =>
   rcases ih with ⟨ih1, ih2⟩
   have lem : (Surface.TyEnv.map (fun x => x.translate) (Surface.TyEnv.map (fun x => x[+1]) Γ)) =
    (Core.TyEnv.map (fun x => x[+1]) (Surface.TyEnv.map (fun x => x.translate) Γ)) := by
    simp[Surface.TyEnv.map, Core.TyEnv.map];
    intros; apply Translation.Ty.Weaken rfl
   apply And.intro
   · apply Core.Term.Determined.lamt ih1
   · apply Core.Typing.lamt
     · apply Core.Kinding.all
       replace jk := Translation.Ty.sound jk h2 rfl
       rcases jk with ⟨_,T,e1, e2, h⟩
       subst e2; subst e1; apply h
     · simp at lem; simp; rw[lem] at ih2; apply ih2

case mtch n Δ Γ s R s' d T d' CTy PTy pats pats' cs cs' _ vhvty _ vhvs pelab stms _ ptms sTy dTy pTys cTys =>
  apply And.intro
  · apply Core.Term.Determined.match;
    apply sTy.1
    apply dTy.1
    intro i; apply (pTys i).1
    intro i; apply (cTys i).1
  · apply Core.Typing.mtch
    apply sTy.2
    apply Translation.ValidTyHeadVariable.sound h2 rfl vhvty
    apply dTy.2
    intro i; apply Translation.ValidHeadVariable.sound2 h2 rfl (pelab i) (vhvs i)
    intro i; apply (pTys i).2
    intro i; apply Translation.StableTypeMatch.sound rfl rfl rfl (stms i)
    intro i; apply (cTys i).2
    intro i; apply Translation.PrefixTypeMatch.sound rfl rfl rfl rfl (ptms i)

case sub mists ch ih =>
  have lem := Translation.Term.typing_spine h2 mists ih.1 ih.2
  rcases lem with ⟨lem1, lem2⟩
  replace h := Translation.synth_term_completeness ch
  rcases h with ⟨h1, h2⟩
  · apply And.intro
    · apply Core.Term.Determined.cast.1
      apply And.intro
      · apply lem1
      · apply h1
    · apply Core.Typing.cast
      · apply lem2
      · apply h2

case annot ih => apply ih

@[simp]
abbrev ElabSoundnessCheckType (G : Surface.GlobalEnv) (G' : Core.GlobalEnv)
  (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) (t : Surface.Term) (t' : Core.Term) (T : Surface.Ty) : Mode -> Prop
| .inf => true
| .chk =>
  ∀ Δ' Γ',
  Δ.translate = Δ' ->
  Γ.translate = Γ' ->

  t.type_chk_translate G G' Δ Γ T = some t' ∧
  t'.Determined ∧
  G'&Δ',Γ' ⊢ t' : T.translate

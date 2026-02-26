import Core.Ty
import Core.Term
import Core.Metatheory.Determined
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
import Core.Term.Spine
import Surface.Typing
import Surface.Metatheory.Inversion
import Translation.Rename

open LeanSubst



theorem Translation.GlobalEnv.lookup_ty_sound {G : Surface.GlobalEnv} : -- maybe generalize this to entry lookup?
  ⊢s G ->
  G.translate = some G' ->
  (∀ (x : String) (T : Surface.Ty) (Δ : Core.KindEnv),
    (Surface.lookup_type G x = some T) ->
    ∃ T' b, (Core.lookup_type G' x = some T' ∧ T.translate = T' ∧ G'&Δ ⊢ T' : .base b)) := by
intro wf h1 i K Δ h2
sorry

theorem Translation.GlobalEnv.is_ctor_sound {G: Surface.GlobalEnv} :
  ⊢s G ->
  G.translate = some G' ->
  Surface.is_ctor G x ->
  Core.is_ctor G' x := by sorry

theorem Translation.GlobalEnv.is_data_sound {G: Surface.GlobalEnv} :
  ⊢s G ->
  G.translate = some G' ->
  Surface.is_data G x ->
  Core.is_data G' x := by
sorry


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
  ⊢s G ->
  G.translate = some G' ->
  T.translate = T' ->
  Surface.ValidTyHeadVariable T (Surface.is_data G) ->
  Core.ValidTyHeadVariable T' (Core.is_data G') := by
intro wf h1 h2 h3
induction h3
case _ sp h4 =>
rcases h4 with ⟨tnf, h4⟩
have lem := Translation.Ty.Spine tnf h2
rcases lem with ⟨sp', lem⟩
simp [Core.ValidTyHeadVariable]
exists (sp.fst)
apply And.intro
· exists sp'
· apply Translation.GlobalEnv.is_data_sound wf h1 h4


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
  A.translate = some A' ->
  T.translate = some T' ->
  R.translate = some R' ->
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
  ⊢s G ->
  G.translate = some G' ->
  Δ.translate = Δ' ->
  Γ.translate = Γ' ->
  t.translate G' Δ' Γ' = some t' ->
  Surface.ValidHeadVariable t (Surface.is_ctor G) ->
  Core.ValidHeadVariable t' (Core.is_ctor G') := by
intro wf h1 h2 h3 h4 h5
induction h5
case _ sp h5 =>
rcases h5 with ⟨tnf, h5⟩
have lem := Translation.Term.Spine tnf h4
rcases lem with ⟨sp', lem⟩
simp [Core.ValidHeadVariable]
exists (sp.fst)
apply And.intro
· exists sp'
· apply Translation.GlobalEnv.is_ctor_sound wf h1 h5


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



-- TODO : Type directed translation?
theorem Translation.Term.Sound (G : Surface.GlobalEnv) :
  ⊢s G ->
  G&Δ,Γ ⊢s t : T ->


  G.translate = some G' ->
  ⊢ G' ->

  Δ.translate = Δ' ->
  Γ.translate = Γ' ->


  ∃ t', t.translate G' Δ' Γ' = some t' ∧
        t'.Determined ∧
        G'&Δ',Γ' ⊢ t' : T.translate := by
intro wf j h1 wfc h2 h3
induction j generalizing Δ' Γ' <;> simp at *
case var Γ x T Δ b h jk =>
  have lem := Translation.TyEnv.sound h3
  replace lem := lem x T h
  replace jk := Translation.Ty.sound wf ⟨jk, h1 , h2⟩
  rcases jk with ⟨K', T', h6, h7, h8⟩
  have h6' := Translation.Kind.sound_base (b := b);
  rcases h6' with ⟨b', h6'⟩;
  rw[h6'] at h6; subst h6
  apply And.intro
  · apply Core.Term.Determined.var
  · subst h7; apply Core.Typing.var lem h8
case global x T Δ b Γ h4 j =>
  have lem := Translation.GlobalEnv.lookup_ty_sound wf h1 x T Δ' h4
  rcases lem with ⟨T', h4, h5, h6, h7⟩
  apply And.intro
  · apply Core.Term.Determined.global
  · subst h6; apply Core.Typing.global h5 h7
case lam Δ A b1 Γ t B j1 j2 ih =>
  have lemA := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lemA with ⟨aK', A', h4a, h5a, h6a⟩
  have lem := Translation.TyEnv.lift_sound h3 j1 h5a
  rcases ih with ⟨t', h10, h11, h12⟩
  have lem := Core.Typing.well_typed_terms_have_base_kinds wfc h12
  subst A'
  rcases lem with ⟨_, jB'⟩
  subst Δ'
  exists (λ[A.translate] t')
  rw[Option.bind_eq_some_iff];
  apply And.intro
  · exists t'
  · apply And.intro
    · apply Core.Term.Determined.lam; assumption
    · have h6' := Translation.Kind.sound_base b1
      rcases h6' with ⟨b1', h6'⟩
      subst aK'; rw[h6'] at h6a
      apply Core.Typing.lam (b := b1')
      assumption
      apply h12
case lamt Δ K P t Γ j1 j2 ih =>
  have lem := Translation.Ty.sound wf ⟨j1, h1, h2⟩
  rcases lem with ⟨K', T', h4, h5, h6⟩
  rcases ih with ⟨t', ih1, ih2, ih3⟩
  simp at *
  exists (Λ[K.translate]t');
  apply And.intro
  · rw[Option.bind_eq_some_iff]; exists t'; simp[Surface.KindEnv.translate] at ih1;
    apply And.intro
    · subst Δ'; subst Γ'
      have lem : (Surface.TyEnv.map (fun x => x.translate) (Surface.TyEnv.map (fun x => x[+1]) Γ)) =
         (Core.TyEnv.map (fun x => x[+1]) (Surface.TyEnv.map (fun x => x.translate) Γ)) := by
         simp[Surface.TyEnv.map, Core.TyEnv.map];
         intros; apply Translation.Ty.Weaken rfl
      rw[lem] at ih1; apply ih1
    · rfl
  · apply And.intro;
    · apply Core.Term.Determined.lamt; assumption
    · subst T'; subst K'; apply Core.Typing.lamt; assumption;
      subst Γ'; simp; rw[Surface.TyEnv.map] at *;
      simp [Surface.KindEnv.translate, Surface.TyEnv.map] at ih3;
      have lem : List.map ((fun x => x.translate) ∘ fun x => x[+1]) Γ =
                 List.map (fun x => x[+1]) (List.map (fun x => x.translate) Γ) := by
        simp; intros; apply Translation.Ty.Weaken rfl
      rw[lem] at ih3; simp at ih3; simp; subst Δ'; apply ih3;


case app Δ A Γ f B a j1 j2 j3 ih1 ih2 =>
  rcases ih1 with ⟨f', ih1f, ih2f, ih3f⟩
  rcases ih2 with ⟨a', ih1a, ih2a, ih3a⟩
  subst Γ'; subst Δ'
  exists (f' • a')
  rw[Option.bind_eq_some_iff]
  apply And.intro
  · exists f';
    apply And.intro;
    · apply ih1f
    · rw[Option.bind_eq_some_iff]; exists a'
  · apply And.intro;
    · apply Core.Term.Determined.app; apply ih2f; apply ih2a
    · have lem := Translation.Ty.sound wf ⟨j1, h1, rfl⟩
      rcases lem with ⟨K', T', e1, e2, jk⟩
      simp at e1; subst K'; subst e2;
      apply Core.Typing.app; apply jk; apply ih3f; apply ih3a

case appt Δ Γ f K P a P' j1 j2 e ih =>
  rcases ih with ⟨f', h4, h5, h6⟩
  have lem := Translation.Ty.sound wf ⟨j2, h1, h2⟩
  rcases lem with ⟨K', a', e1, lem1, lem2⟩
  subst K'; subst a'; subst Γ'; subst Δ'; subst P'
  exists (f' •[a.translate])
  apply And.intro
  · rw[Option.bind_eq_some_iff]; exists f'
  · apply And.intro
    · apply Core.Term.Determined.appt; assumption
    · apply Core.Typing.appt
      apply h6
      apply lem2
      apply Translation.Ty.beta rfl rfl

case mtch n Δ Γ s R c T CTy PTy pats cs sj vhvR cj vhvps patsj stmPTys csj ptms ih1 ih2 ih3 ih4 =>
  rcases ih1 with ⟨s', ih1s, ih2s, ih3s⟩
  rcases ih2 with ⟨d', ih1c, ih2c, ih3c⟩

  replace ih3 := quantifier_beast_lemma ih3
  replace ih4 := quantifier_beast_lemma ih4

  rcases ih3 with ⟨ps', ih3i, ih3ii, ih3iii⟩
  rcases ih4 with ⟨cs', ih4i, ih4ii, ih4iii⟩

  exists (match! n s' ps' cs' d')

  rw[Option.bind_eq_some_iff]
  apply And.intro
  · exists s'
    apply And.intro
    · subst Δ'; subst Γ'; assumption
    · rw[Option.bind_eq_some_iff]; exists ps'
      apply And.intro
      · unfold Vect.seq
        generalize zdef : Vect.seq_lemma (fun i => Surface.Term.translate G' Δ' Γ' (pats i)) = z at *
        cases z <;> simp at *
        case _ z =>
          rcases z with ⟨x, z⟩
          replace ih3i := ih3i x
          subst Δ'; subst Γ'
          rw[ih3i] at z; simp at z
        case _ z =>
          funext; case _ x =>
          replace ih3i := ih3i x
          subst Δ'; subst Γ';
          simp at *; simp only [ih3i]; simp
      · rw[Option.bind_eq_some_iff]; exists cs'
        apply And.intro
        · unfold Vect.seq
          generalize zdef : Vect.seq_lemma (fun i => Surface.Term.translate G' Δ' Γ' (cs i)) = z at *
          cases z <;> simp at *
          case _ z =>
            rcases z with ⟨x, z⟩
            replace ih4i := ih4i x
            subst Δ'; subst Γ'
            rw[ih4i] at z; simp at z
          case _ z =>
            funext; case _ x =>
            replace ih4i := ih4i x
            subst Δ'; subst Γ';
            simp only [ih4i]; simp
        · rw[Option.bind_eq_some_iff]; exists d'
          apply And.intro
          · subst Δ'; subst Γ'; assumption
          · rfl
  · apply And.intro
    · apply Core.Term.Determined.match ih2s ih2c ih3ii ih4ii
    · subst Δ'; subst Γ'
      apply Core.Typing.mtch
            (CTy := λ i => (CTy i).translate) (PTy := λ i => (PTy i).translate) (pats := ps') (cs := cs')
      · apply ih3s
      · apply Translation.ValidTyHeadVariable.sound wf h1 rfl vhvR
      · assumption
      · intro i; apply Translation.ValidHeadVariable.sound wf h1 rfl rfl (ih3i i) (vhvps i)
      · apply ih3iii
      · intro i; apply Translation.StableTypeMatch.sound rfl rfl rfl (stmPTys i)
      · apply ih4iii
      · intro i; apply Translation.PrefixTypeMatch.sound rfl rfl rfl rfl (ptms i)

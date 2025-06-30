import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Term.Variant
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Progress
import SystemFD.Metatheory.Preservation
import SystemFD.Metatheory.Inversion

inductive HssdiVariant where
| wf | prf

@[simp]
abbrev HssdiArgs : HssdiVariant -> Type
| .wf => Unit
| .prf => Term

inductive Hssdi : (v : HssdiVariant) -> Ctx Term -> HssdiArgs v -> Prop where
| nil : Hssdi .wf [] ()
| cons_normal :
  f.variant ∉ [.term, .inst] ->
  Hssdi .wf (f :: Γ) ()
| cons_term :
  Hssdi .prf Γ t ->
  Hssdi .wf (.term A t :: Γ) ()
| cons_inst :
  Hssdi .prf Γ t ->
  Hssdi .wf (.inst A t :: Γ) ()
| var :
  Hssdi .wf Γ () ->
  Hssdi .prf Γ #x
| type :
  Hssdi .wf Γ () ->
  Hssdi .prf Γ ★
| ctor1 :
  Hssdi .prf Γ t ->
  Hssdi .prf Γ (.ctor1 v t)
| ctor2 :
  v ∉ [.choice, .app] ->
  Hssdi .prf Γ t1 ->
  Hssdi .prf Γ t2 ->
  Hssdi .prf Γ (.ctor2 v t1 t2)
| app :
  Γ ⊢ f : (A -t> B) ->
  (∀ x sp1, .some (x, sp1) = A.neutral_form ->
    Γ.is_opent x ->
    ∃ y, ∃ sp2, .some (y, sp2) = a.neutral_form
    ∧ (Γ.is_insttype y ∨ Γ.is_type y)
  ) ->
  Hssdi .prf Γ f ->
  Hssdi .prf Γ a ->
  Hssdi .prf Γ (f `@ a)
| choice1 :
  Hssdi .prf Γ t1 ->
  Hssdi .prf Γ (t1 ⊕ t2)
| choice2 :
  Hssdi .prf Γ t2 ->
  Hssdi .prf Γ (t1 ⊕ t2)
| bind2 :
  -- Hssdi .prf Γ A ->
  -- Hssdi .prf (bind2_frame A v :: Γ) t2 ->
  Hssdi .prf Γ (.bind2 v A t)
| eq : Hssdi .prf Γ (.eq A u v)
| ite :
  Hssdi .prf Γ s ->
  Hssdi .prf Γ b ->
  Hssdi .prf Γ t ->
  Hssdi .prf Γ (.ite p s b t)
| guard :
  .some (y, sp1) = Term.neutral_form p ->
  (∀ x sp2, .some (x, sp2) = Term.neutral_form s ->
    (x = y ∧ .some q = prefix_equal sp1 sp2)
    ∨ ¬ Γ.is_stable_red x
  ) ->
  Hssdi .prf Γ s ->
  Hssdi .prf Γ t ->
  Hssdi .prf Γ (.guard p s t)
| letterm :
  Hssdi .prf Γ t ->
  Hssdi .prf Γ b ->
  Hssdi .prf Γ (.letterm A t b)

theorem hssdi_not_zero : ¬ Hssdi .prf Γ `0 := by
intro h; cases h

@[simp]
abbrev HssdiPreservationLemmaType (Γ : Ctx Term) : (v : HssdiVariant) -> HssdiArgs v -> Prop
| .prf => λ t => ∀ t', Red Γ t t' -> Hssdi .prf Γ t'
| .wf => λ () => True

theorem hssdi_preservation_lemma : Hssdi v Γ ix -> HssdiPreservationLemmaType Γ v ix := by
intro j
induction j <;> simp at *
case app j1 j2 j3 ih1 ih2 h =>
  intro t' r
  cases r
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => simp at *
  case _ => cases j2
  case _ => simp at *
  case _ c1 c2 _ _ =>
    cases j1; case _ q1 q2 q3 q4 =>
    cases j2; simp at *
    case _ j2 =>
      apply Hssdi.choice1
      apply Hssdi.app q3 _ j2 j3; simp; apply h
    case _ j2 =>
      apply Hssdi.choice2
      apply Hssdi.app q4 _ j2 j3; simp; apply h
  case _ => simp at *
repeat sorry

@[simp]
abbrev HssdiSoundLemmaType (Γ : Ctx Term) : (v : HssdiVariant) -> HssdiArgs v -> Prop
| .prf => λ t => ¬ Red Γ t `0
| .wf => λ () => True

theorem hssdi_sound_lemma : Hssdi v Γ ix -> HssdiSoundLemmaType Γ v ix := by
have lem1 : ∀ t sp, `0 = t.apply_spine sp -> t = `0 ∧ sp = [] := by
  intro t sp h
  induction sp generalizing t <;> simp at *
  case _ => rw [h]
  case _ hd tl ih =>
    cases hd; case _ sv a =>
    cases sv
    all_goals (
      simp at h
      replace ih := ih _ h
      cases ih; case _ e1 e2 =>
      injection e1
    )
have lem2 : ∀ (sp1 sp2 : List (SpineVariant × Term)), .some [] = prefix_equal sp1 sp2 -> sp2 = [] := by
  sorry
intro h
induction h
case nil => sorry
case cons_normal => sorry
case cons_term => sorry
case cons_inst => sorry
case var => sorry
case type => sorry
case ctor1 => sorry
case ctor2 => sorry
case app => sorry
case choice1 => sorry
case choice2 => sorry
case bind2 => sorry
case eq => sorry
case ite => sorry
case guard ih1 ih2 =>
  simp at *; intro h
  generalize zdef : `0 = z at *
  cases h
  case _ => sorry
  case _ => sorry
  case _ h _ => simp at h
  case _ h => simp at h
  case _ => injection zdef
  case _ => sorry
  case _ => injection zdef
case letterm => sorry

theorem hssdi_sound : Hssdi .prf Γ t -> ¬ Red Γ t `0 := by
intro h r
have lem := hssdi_sound_lemma h; simp at lem
apply lem r

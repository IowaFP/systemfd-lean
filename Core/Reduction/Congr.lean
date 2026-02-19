import LeanSubst
import Core.Term
import Core.Reduction.Definition

open LeanSubst
namespace Core
-- Ctor2 Congr1
@[simp]
theorem Ctor2Variant.congr1_app : congr1 (app b) = true := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_cast : congr1 cast = false := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_seq : congr1 seq = true := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_appc : congr1 appc = true := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_apptc : congr1 apptc = true := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_arrowc : congr1 arrowc = true := by simp [congr1]

@[simp]
theorem Ctor2Variant.congr1_choice : congr1 choice = true := by simp [congr1]

-- Ctor2 Congr2
@[simp]
theorem Ctor2Variant.congr2_app : congr2 (app .closed) = false := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_appo : congr2 (app .open) = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_cast : congr2 cast = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_seq : congr2 seq = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_appc : congr2 appc = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_apptc : congr2 apptc = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_arrowc : congr2 arrowc = true := by simp [congr2]

@[simp]
theorem Ctor2Variant.congr2_choice : congr2 choice = true := by simp [congr2]

-- TyBind Congr
@[simp]
theorem TyBindVariant.congr_lamt : congr lamt = false := by simp [congr]

@[simp]
theorem TyBindVariant.congr_allc : congr allc = true := by simp [congr]

theorem Red.spine_congr_step :
  Red G t t' ->
  Red G (t.apply sp) (t'.apply sp)
:= by
  intro h
  induction sp generalizing t t'
  case nil => simp [Term.apply]; exact h
  case cons hd tl ih =>
    cases hd
    case type A =>
      simp [Term.apply]
      apply ih; apply Red.ctor1_congr h
    case term a =>
      simp [Term.apply]
      apply ih; apply Red.ctor2_congr1 _ h
      simp
    case oterm a =>
      simp [Term.apply]
      apply ih; apply Red.ctor2_congr1 _ h
      simp

theorem Red.spine_congr :
  Star (Red G) t t' ->
  Star (Red G) (t.apply sp) (t'.apply sp)
:= by
  intro h
  induction h
  case _ => apply Star.refl
  case _ y z h1 h2 ih =>
    apply Star.step ih
    apply spine_congr_step h2
end Core

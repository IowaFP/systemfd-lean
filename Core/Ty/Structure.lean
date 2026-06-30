import Core.Ty.Definition
import Core.Ty.Substitution
import Core.Ty.BEq

open LeanSubst
open Lilac

namespace Core

def Ty.spine : Ty -> Option (String × List Ty)
| gt#x => return (x, [])
| app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [a])
| _ => none

@[simp, grind =]
theorem Ty.spine_arrow {A B : Ty} : (A -:> B).spine = none := by simp [spine]

@[simp, grind =]
theorem Ty.spine_all : (∀[K] A).spine = none := by simp [spine]

@[simp, grind =]
theorem Ty.spine_eq : (A ~[K]~ B).spine = none := by simp [spine]

theorem Ty.spine_subst {R : Ty} (σ : Subst Ty)
  : R.spine = some (x, sp) -> R[σ].spine = some (x, sp[σ])
:= by
  intro h
  fun_induction Ty.spine generalizing x sp
  case _ => simp at h; rcases h with ⟨e1, e2⟩; subst e1; subst e2; simp [Ty.spine]
  case _ ih =>
    simp at h; rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨x', sp'⟩, h2, h⟩
    simp at h; replace ih := ih h2
    simp[Ty.spine]; rw[Option.bind_eq_some_iff];
    exists (x', sp'[σ]); simp;
    apply And.intro
    · apply ih
    · apply And.intro;
      · apply h.1
      · rw[<-h.2]; simp
  cases h

theorem Ty.spine_ren {R : Ty} (r : Ren Ty)
  : R.spine = some (x, sp) -> R⟨r⟩.spine = some (x, sp⟨r⟩)
:= by
  intro h
  fun_induction Ty.spine generalizing x sp <;> simp [spine] at *
  case _ =>
    rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
  case _ ih =>
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨x', sp'⟩, h2, h⟩
    simp at h; rcases h with ⟨e1, e2⟩; subst e1; subst e2;
    rw[Option.bind_eq_some_iff];
    replace ih := ih h2
    exists (x', sp'⟨r⟩)
    apply And.intro
    · apply ih
    · simp


theorem quantifier_bundle :
  (∀ (a : α) (b : β) , ¬ t = .some (a, b)) <-> ∀ (h : α × β), ¬ t = some h
  := by
  apply Iff.intro
  · intro h p h1
    replace h := h p.1 p.2; simp at h; apply h h1
  · intro h a b;
    apply h (a, b)

theorem Ty.spine_ren_none {R : Ty} (r : Ren Ty)
  : R.spine = none -> R⟨r⟩.spine = none
:= by
  intro h
  induction R <;> simp [spine] at *
  case _ f _ ih _ =>
    rw[quantifier_bundle, option_lemma] at *
    apply ih h

def Ty.is_all_some : Ty -> Option (Kind × Ty)
| .all K B => return (K, B)
| _ => none

def Ty.is_all_some_sound {T : Ty} :
  T.is_all_some = .some (K, T1) ->
  T = ∀[K] T1 := by
intro h
cases T <;> simp [Ty.is_all_some] at *
assumption


def Ty.is_arrow_some : Ty -> Option (Ty × Ty)
| .arrow A B => return (A, B)
| _ => none

def Ty.is_arrow_some_sound {T : Ty} :
  T.is_arrow_some = .some (T1, T2) ->
  T = T1 -:> T2 := by
intro h
cases T <;> simp [Ty.is_arrow_some] at *
assumption

def Ty.is_eq_some : Ty -> Option (Kind × Ty × Ty)
| .eq K A B => return (K, A, B)
| _ => none

def Ty.is_eq_some_sound {T : Ty} :
  T.is_eq_some = some (K, A, B) ->
  T = (A ~[K]~ B) := by
intro h;
cases T <;> simp [Ty.is_eq_some] at *
assumption

def Ty.is_app_some : Ty -> Option (Ty × Ty)
| .app A B => return (A, B)
| _ => none

def Ty.is_app_some_sound {T : Ty} :
  T.is_app_some = some (A, B) ->
  T = (A • B) := by
intro h;
cases T <;> simp [Ty.is_app_some] at *
assumption

end Core

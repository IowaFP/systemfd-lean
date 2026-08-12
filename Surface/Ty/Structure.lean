import LeanSubst
import Surface.Ty.Definition
import Surface.Ty.Substitution
import Surface.Ty.BEq
import Core.Util

open LeanSubst
namespace Surface

def Ty.spine : Ty -> Option (String × List Ty)
| gt`#x => return (x, [])
| app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [a])
| _ => none

@[simp, grind =]
theorem Ty.spine_arrow {A B : Ty} : (A `-:> B).spine = none := by simp [spine]

@[simp, grind =]
theorem Ty.spine_all : (`∀[K] A).spine = none := by simp [spine]

@[simp, grind =]
theorem Ty.spine_then : (A `=:> B).spine = none := by simp [spine]

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
  T = `∀[K] T1 := by
intro h
cases T <;> simp [Ty.is_all_some] at *
assumption

def Ty.is_then_some : Ty -> Option (Ty × Ty)
| A `=:> B => return (A, B)
| _ => none

def Ty.is_arrow_some_sound {T : Ty} :
  T.is_then_some = .some (T1, T2) ->
  T = T1 `=:> T2 := by
intro h
cases T <;> simp [Ty.is_then_some] at *
assumption

def Ty.is_app_some : Ty -> Option (Ty × Ty)
| .app A B => return (A, B)
| _ => none

def Ty.is_app_some_sound {T : Ty} :
  T.is_app_some = some (A, B) ->
  T = (A `• B) := by
intro h;
cases T <;> simp [Ty.is_app_some] at *
assumption

def Ty.subterms : Ty -> List Ty
| .app x y => x.subterms ++ y.subterms ++ [.app x y]
| .arrow x y => x.subterms ++ y.subterms ++ [.arrow x y]
| .then x y => x.subterms ++ y.subterms ++ [.then x y]
| x => [x]


def Ty.mkApps (T : Ty) : List Ty -> Ty := List.foldl (init := T) (λ acc t => acc `• t)

def Ty.mkApps_nats (T : Ty) : List Nat -> Ty := List.foldl (init := T) (λ acc t => acc `• t`#t)

end Surface

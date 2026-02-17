import LeanSubst
import Surface.Ty.Definition
import Surface.Ty.Substitution
import Surface.Ty.BEq

open LeanSubst

def Surface.Ty.spine : Ty -> Option (String × List Ty)
| gt#x => return (x, [])
| app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [a])
| _ => none

def Surface.Ty.apply (t : Ty) : List Ty -> Ty
| [] => t
| .cons a tl => (t • a).apply tl

def Surface.Ty.arity : Ty -> Nat
| arrow _ B => B.arity + 1
| ∀[_] P => P.arity + 1
| _ => 0

inductive Surface.TeleElem
| kind (K : Surface.Kind)
| ty (A : Surface.Ty)
deriving Repr

def Surface.Telescope := List Surface.TeleElem

def Surface.Telescope.extend (Γ : List Surface.Ty) : Telescope -> List Surface.Ty
| [] => Γ
| .cons (.kind _) te => extend Γ te
| .cons (.ty A) te => extend (A::Γ) te

def Surface.Telescope.rmap (lf : Endo Ren) (r : Ren) : Telescope -> Telescope
| [] => []
| .cons (.kind K) te => .cons (.kind K) (rmap lf r te)
| .cons (.ty A) te => .cons (.ty A[r]) (rmap lf (lf r) te)

instance : RenMap Surface.Telescope where
  rmap := Surface.Telescope.rmap

def Surface.Telescope.smap (lf : Endo (Subst Surface.Ty)) (σ : Subst Surface.Ty) : Surface.Telescope -> Surface.Telescope
| [] => []
| .cons (.kind K) te => .cons (.kind K) (smap lf σ te)
| .cons (.ty A) te => .cons (.ty A[σ]) (smap lf (lf σ) te)

instance : SubstMap Surface.Telescope Surface.Ty where
  smap := Surface.Telescope.smap

def Surface.Ty.telescope : Ty -> Telescope  × Ty
| .arrow A B =>
  let (tys, b) := B.telescope
  (.ty A :: tys, b)
| .all K B =>
  let (tys, b) := B.telescope
  (.kind K :: tys, b)
| t => ([], t)

def Surface.Telescope.count_binders (t : Surface.Telescope) : Nat :=
  t.foldl (λ acc x => match x with
                  | .kind _ => acc + 1
                  | _ => acc) 0

def Surface.Ty.from_telescope : List Surface.TeleElem -> Ty -> Ty
| .nil , t => t
| .cons (.ty A) tys, t =>
  let r := t.from_telescope tys
  A -:> r
| .cons (.kind K) tys, t =>
  let r := t.from_telescope tys
  ∀[K] r

@[simp]
theorem Surface.Ty.Spine.apply_subst {t : Ty} {sp : List Ty} : (t.apply sp)[σ] = (t[σ]).apply (sp.map (·[σ])) := by
  induction sp generalizing t <;> simp [Surface.Ty.apply]
  case cons hd tl ih => rw [ih]; simp

@[simp]
theorem Surface.Ty.Spine.app_eq :
  (f • a).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [a] ∧ f.spine = some (x, sp')
:= by
  apply Iff.intro <;> intro h
  case _ =>
    simp [Surface.Ty.spine] at h
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [e1]; exists sp'
  case _ =>
    rcases h with ⟨sp', e1, e2⟩; subst e1
    simp [Surface.Ty.spine]
    rw [Option.bind_eq_some_iff]; apply Exists.intro (x, sp')
    apply And.intro e2; simp

theorem Surface.Ty.Spine.apply_type {t : Ty} : t.apply sp • a = t.apply (sp ++ [a]) := by
  induction sp generalizing t <;> simp [Surface.Ty.apply]
  case cons hd tl ih => rw [ih]

theorem Surface.Ty.Spine.apply_eq
  : t.spine = some (x, sp) -> t = (gt#x).apply sp
:= by
  intro h
  fun_induction Surface.Ty.spine generalizing x sp <;> simp at *
  case _ y =>
    rcases h with ⟨e1, e2⟩; subst e1 e2
    simp [Surface.Ty.apply]
  case _ ih =>
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [ih e1, apply_type]

theorem Surface.Ty.Spine.apply_compose {t : Ty}
  : t.spine = some (x, sp1) -> (t.apply sp2).spine = some (x, sp1 ++ sp2)
:= by
  intro h; induction sp2 generalizing t x sp1
  simp [Surface.Ty.apply]; exact h
  case _ a tl ih =>
  have lem : (t • a).spine = some (x, sp1 ++ [a]) := by simp; exact h
  replace ih := ih lem; simp at ih; exact ih

@[simp]
theorem Surface.Ty.Spine.apply_eta : ((gt#x).apply sp).spine = some (x, sp) := by
  have lem := @apply_compose x [] sp gt#x (by simp [Surface.Ty.spine])
  simp at lem; exact lem

import LeanSubst
import Core.Ty.Definition
import Core.Ty.Substitution
import Core.Ty.BEq

open LeanSubst

namespace Core
def Ty.spine : Ty -> Option (String × List Ty)
| gt#x => return (x, [])
| app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [a])
| _ => none

def Ty.apply (t : Ty) : List Ty -> Ty
| [] => t
| .cons a tl => (t • a).apply tl

def Ty.arity : Ty -> Nat
| arrow _ B => B.arity + 1
| ∀[_] P => P.arity + 1
| _ => 0

inductive Telescope where
| nil : Telescope
| kind : Kind -> Telescope -> Telescope
| ty : Ty -> Telescope -> Telescope

def Telescope.rmap (lf : Endo Ren) (r : Ren) : Telescope -> Telescope
| nil => nil
| kind K te => kind K (rmap lf (lf r) te)
| ty A te => ty A[r] (rmap lf r te)

instance : RenMap Telescope where
  rmap := Telescope.rmap

def Telescope.smap (lf : Endo (Subst Ty)) (σ : Subst Ty) : Telescope -> Telescope
| nil => nil
| kind K te => kind K (smap lf (lf σ) te)
| ty A te => ty A[σ] (smap lf σ te)

instance : SubstMap Telescope Ty where
  smap := Telescope.smap

@[simp]
theorem Telescope.subst_nil : (nil)[σ:Ty] = nil := by
  simp [Subst.apply, SubstMap.smap, Telescope.smap]

@[simp]
theorem Telescope.subst_kind : (kind K te)[σ:Ty] = kind K te[σ.lift:_] := by
  simp [Subst.apply, SubstMap.smap, Telescope.smap]

@[simp]
theorem Telescope.subst_ty : (ty A te)[σ:Ty] = ty A[σ:_] te[σ:_] := by
  simp [Subst.apply, SubstMap.smap, Telescope.smap]

def Telescope.extend (Γ : List Ty) : Telescope -> List Ty
| nil => Γ
| kind _ te => extend Γ te
| ty A te => extend (A::Γ) te

def Ty.telescope : Ty -> Telescope  × Ty
| .arrow A B =>
  let (tys, b) := B.telescope
  (.ty A tys, b)
| .all K B =>
  let (tys, b) := B.telescope
  (.kind K tys, b)
| t => (.nil, t)

-- def Telescope.count_binders (t : Telescope) : Nat :=
--   t.foldl (λ acc x => match x with
--                   | .kind _ => acc + 1
--                   | _ => acc) 0

def Ty.from_telescope : Telescope -> Ty -> Ty
| .nil , t => t
| .ty A tys, t =>
  let r := t.from_telescope tys
  A -:> r
| .kind K tys, t =>
  let r := t.from_telescope tys
  ∀[K] r

@[simp]
theorem Ty.Spine.apply_subst {t : Ty} {sp : List Ty} : (t.apply sp)[σ] = (t[σ]).apply (sp.map (·[σ])) := by
  induction sp generalizing t <;> simp [Ty.apply]
  case cons hd tl ih => rw [ih]; simp

@[simp]
theorem Ty.Spine.app_eq :
  (f • a).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [a] ∧ f.spine = some (x, sp')
:= by
  apply Iff.intro <;> intro h
  case _ =>
    simp [Ty.spine] at h
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [e1]; exists sp'
  case _ =>
    rcases h with ⟨sp', e1, e2⟩; subst e1
    simp [Ty.spine]
    rw [Option.bind_eq_some_iff]; apply Exists.intro (x, sp')
    apply And.intro e2; simp

theorem Ty.Spine.apply_type {t : Ty} : t.apply sp • a = t.apply (sp ++ [a]) := by
  induction sp generalizing t <;> simp [Ty.apply]
  case cons hd tl ih => rw [ih]

theorem Ty.Spine.apply_eq
  : t.spine = some (x, sp) -> t = (gt#x).apply sp
:= by
  intro h
  fun_induction Ty.spine generalizing x sp <;> simp at *
  case _ y =>
    rcases h with ⟨e1, e2⟩; subst e1 e2
    simp [Ty.apply]
  case _ ih =>
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [ih e1, apply_type]

theorem Ty.Spine.apply_compose {t : Ty}
  : t.spine = some (x, sp1) -> (t.apply sp2).spine = some (x, sp1 ++ sp2)
:= by
  intro h; induction sp2 generalizing t x sp1
  simp [Ty.apply]; exact h
  case _ a tl ih =>
  have lem : (t • a).spine = some (x, sp1 ++ [a]) := by simp; exact h
  replace ih := ih lem; simp at ih; exact ih

@[simp]
theorem Ty.Spine.apply_eta : ((gt#x).apply sp).spine = some (x, sp) := by
  have lem := @apply_compose x [] sp gt#x (by simp [Ty.spine])
  simp at lem; exact lem

end Core

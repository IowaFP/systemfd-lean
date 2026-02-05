import LeanSubst
import Core.Util
import Core.Term.Definition
import Core.Term.Substitution
import Core.Term.BEq

open LeanSubst


inductive SpineElem : Type where
| type (x : Ty)
| term (x : Term)
| oterm (x : Term)
deriving Repr


@[simp]
def SpineElem.rmap (_ : Endo Ren) (r : Ren) : SpineElem -> SpineElem
| type T => type T[r:Ty]
| term t => term t[r:Term]
| oterm t => oterm t[r:Term]

instance : RenMap SpineElem where
  rmap := SpineElem.rmap

@[simp]
def SpineElem.Ty.smap (_ : Endo (Subst Ty)) (σ : Subst Ty) : SpineElem -> SpineElem
| type T => type T[σ]
| term t => term t[σ:Ty]
| oterm t => oterm t[σ:Ty]

instance : SubstMap SpineElem Ty where
  smap := SpineElem.Ty.smap

@[simp]
theorem SpineElem.Ty.subst_type : (type T)[σ:Ty] = type T[σ] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem SpineElem.Ty.subst_term : (term T)[σ:Ty] = term T[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem SpineElem.Ty.subst_oterm : (oterm T)[σ:Ty] = oterm T[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
def SpineElem.Term.smap (_ : Endo (Subst Term)) (σ : Subst Term) : SpineElem -> SpineElem
| type T => type T
| term t => term t[σ]
| oterm t => oterm t[σ]

instance : SubstMap SpineElem Term where
  smap := SpineElem.Term.smap

@[simp]
theorem SpineElem.Term.subst_type : (type T)[σ:Term] = type T := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem SpineElem.Term.subst_term : (term T)[σ:Term] = term T[σ:_] := by
  simp [Subst.apply, SubstMap.smap]

@[simp]
theorem SpineElem.Term.subst_oterm : (oterm T)[σ:Term] = oterm T[σ:_] := by
  simp [Subst.apply, SubstMap.smap]


def SpineElem.beq : SpineElem -> SpineElem -> Bool
| type A, type B => A == B
| term a, term b => a == b
| oterm a, oterm b => a == b
| _, _ => false

instance instBEq_SpineElem : BEq SpineElem where
  beq := SpineElem.beq

instance instReflBEq_SpineElem : ReflBEq SpineElem where
  rfl := by
    intro a; cases a <;> simp [SpineElem.beq, instBEq_SpineElem] at *

instance instLawfulBEq_SpineElem : LawfulBEq SpineElem where
  eq_of_beq := by
    intro a b; cases a <;> simp [instBEq_SpineElem, SpineElem.beq] at *
    all_goals (cases b <;> simp at *)



def Term.spine : Term -> Option (String × List SpineElem)
| g#x => return (x, [])
| ctor2 (.app .closed) f a => do
  let (x, sp) <- spine f
  (x, sp ++ [.term a])
| ctor2 (.app .open) f a => do
  let (x, sp) <- spine f
  (x, sp ++ [.oterm a])
| f •[a] => do
  let (x, sp) <- spine f
  (x, sp ++ [.type a])
| _ => none

def Term.apply (t : Term) : List SpineElem -> Term
| [] => t
| .cons (.type A) tl => (t •[A]).apply tl
| .cons (.term a) tl => (t • a).apply tl
| .cons (.oterm a) tl => (t ∘[a]).apply tl

@[simp]
theorem Spine.apply_subst_type {t : Term} : (t.apply sp)[σ:Ty] = (t[σ:_]).apply (sp.map (·[σ:_])) := by
  induction sp generalizing t <;> simp [Term.apply]
  case cons hd tl ih =>
    cases hd <;> simp [Term.apply]
    all_goals rw [ih]; simp

@[simp]
theorem Spine.apply_subst {t : Term} : (t.apply sp)[σ] = (t[σ]).apply (sp.map (·[σ:Term])) := by
  induction sp generalizing t <;> simp [Term.apply]
  case cons hd tl ih =>
    cases hd <;> simp [Term.apply]
    all_goals rw [ih]; simp

macro "spine_app_eq_solve" x:term : tactic => `(tactic| {
  apply Iff.intro <;> intro h
  case _ =>
    simp [Term.spine] at h
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [e1]; exists sp'
  case _ =>
    rcases h with ⟨sp', e1, e2⟩; subst e1
    simp [Term.spine]
    rw [Option.bind_eq_some_iff]; apply Exists.intro ($x, sp')
    apply And.intro e2; simp
})

@[simp]
theorem Spine.app_closed_eq {f a : Term} :
  (f • a).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [.term a] ∧ f.spine = some (x, sp')
:= by spine_app_eq_solve x

@[simp]
theorem Spine.app_open_eq {f a : Term} :
  (f ∘[a]).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [.oterm a] ∧ f.spine = some (x, sp')
:= by spine_app_eq_solve x

@[simp]
theorem Spine.appt_eq {f : Term} :
  (f •[a]).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [.type a] ∧ f.spine = some (x, sp')
:= by spine_app_eq_solve x

macro "spine_apply_solve" sp:Lean.Parser.Tactic.elimTarget "," t:term : tactic => `(tactic| {
  induction $sp generalizing $t <;> simp [Term.apply]
  case cons hd tl ih _ =>
  cases hd <;> simp [Term.apply]
  all_goals rw [ih]
})

theorem Spine.apply_term {t : Term} : t.apply sp • a = t.apply (sp ++ [.term a]) := by
  spine_apply_solve sp, t

theorem Spine.apply_oterm {t : Term} : t.apply sp ∘[a] = t.apply (sp ++ [.oterm a]) := by
  spine_apply_solve sp, t

theorem Spine.apply_type {t : Term} : t.apply sp •[a] = t.apply (sp ++ [.type a]) := by
  spine_apply_solve sp, t

macro "spine_apply_eq_case_solve"
  h:term ","
  ih:term ","
  ap:Lean.Parser.Tactic.rwRule : tactic =>
`(tactic| {
  replace h := $h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨q, e1, e2⟩
  rcases q with ⟨y, sp'⟩; simp at e2
  rcases e2 with ⟨e2, e3⟩; subst e2 e3
  replace ih := $ih e1
  rw [ih, $ap]
})

theorem Spine.apply_eq
  : t.spine = some (x, sp) -> t = (g#x).apply sp
:= by
  intro h
  fun_induction Term.spine generalizing x sp <;> simp at *
  case _ y =>
    rcases h with ⟨e1, e2⟩; subst e1 e2
    simp [Term.apply]
  case _ ih => spine_apply_eq_case_solve h, ih, apply_term
  case _ ih => spine_apply_eq_case_solve h, ih, apply_oterm
  case _ ih => spine_apply_eq_case_solve h, ih, apply_type

theorem Spine.apply_compose {t : Term}
  : t.spine = some (x, sp1) -> (t.apply sp2).spine = some (x, sp1 ++ sp2)
:= by
  intro h; induction sp2 generalizing t x sp1
  simp [Term.apply]; exact h
  case _ hd tl ih =>
  cases hd <;> simp [Term.apply] at *
  case _ T =>
    have lem : (t •[T]).spine = some (x, sp1 ++ [.type T]) := by simp; exact h
    replace ih := ih lem; simp at ih; exact ih
  case _ a =>
    have lem : (t • a).spine = some (x, sp1 ++ [.term a]) := by simp; exact h
    replace ih := ih lem; simp at ih; exact ih
  case _ a =>
    have lem : (t ∘[a]).spine = some (x, sp1 ++ [.oterm a]) := by simp; exact h
    replace ih := ih lem; simp at ih; exact ih

@[simp]
theorem Spine.apply_eta : ((g#x).apply sp).spine = some (x, sp) := by
  have lem := @apply_compose x [] sp g#x (by simp [Term.spine])
  simp at lem; exact lem


theorem Spine.apply_spine_compose {t : Term}:
  t.apply (s1 ++ s2) = (t.apply s1).apply s2 := by
induction t, s1 using Term.apply.induct generalizing s2 <;> simp [Term.apply] at *
all_goals (case _ ih => apply ih)

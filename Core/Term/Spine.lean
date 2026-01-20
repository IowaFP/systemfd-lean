import LeanSubst
import Core.Util
import Core.Term.Definition
import Core.Term.Beq

open LeanSubst

inductive SpineElem : Type where
| type (x : Ty)
| term (x : Term)
| oterm (x : Term)
deriving Repr

def SpineElem.beq : SpineElem -> SpineElem -> Bool
| type A, type B => A == B
| term a, term b => a == b
| oterm a, oterm b => a == b
| _, _ => false

instance : BEq SpineElem where
  beq := SpineElem.beq

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

macro "spine_app_eq_solve" x:term : tactic => `(tactic| {
  apply Iff.intro <;> intro h
  case _ =>
    simp [Term.spine] at h
    replace h := Eq.symm h
    rw [Option.bind_eq_some_iff] at h
    rcases h with ⟨q, e1, e2⟩
    rcases q with ⟨y, sp'⟩; simp at e2
    rcases e2 with ⟨e2, e3⟩; subst e2 e3
    rw [e1]; exists sp'
  case _ =>
    rcases h with ⟨sp', e1, e2⟩; subst e1
    simp [Term.spine]; apply Eq.symm
    rw [Option.bind_eq_some_iff]; apply Exists.intro ($x, sp')
    apply And.intro (Eq.symm e2); simp
})

@[simp]
theorem Spine.app_closed_eq {f a : Term} :
  some (x, sp) = (f • a).spine
  <-> ∃ sp', sp = sp' ++ [.term a] ∧ some (x, sp') = f.spine
:= by spine_app_eq_solve x

@[simp]
theorem Spine.app_open_eq {f a : Term} :
  some (x, sp) = (f ∘[a]).spine
  <-> ∃ sp', sp = sp' ++ [.oterm a] ∧ some (x, sp') = f.spine
:= by spine_app_eq_solve x

@[simp]
theorem Spine.appt_eq {f : Term} :
  some (x, sp) = (f •[a]).spine
  <-> ∃ sp', sp = sp' ++ [.type a] ∧ some (x, sp') = f.spine
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
  replace h := Eq.symm $h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨q, e1, e2⟩
  rcases q with ⟨y, sp'⟩; simp at e2
  rcases e2 with ⟨e2, e3⟩; subst e2 e3
  replace ih := $ih (Eq.symm e1)
  rw [ih, $ap]
})

theorem Spine.apply_eq  :
  some (x, sp) = t.spine -> t = (g#x).apply sp
:= by
  intro h
  fun_induction Term.spine generalizing x sp <;> simp at *
  case _ y =>
    rcases h with ⟨e1, e2⟩; subst e1 e2
    simp [Term.apply]
  case _ ih => spine_apply_eq_case_solve h, ih, apply_term
  case _ ih => spine_apply_eq_case_solve h, ih, apply_oterm
  case _ ih => spine_apply_eq_case_solve h, ih, apply_type

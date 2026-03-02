import LeanSubst
import Core.Util
import Surface.Term.Definition
import Surface.Term.Substitution
import Surface.Term.BEq

open LeanSubst
namespace Surface

inductive SpineElem : Type where
| type (x : Ty)
| term (x : Term)
deriving Repr

@[simp]
def SpineElem.rmap (r : Ren) : SpineElem -> SpineElem
| type T => type T[r:Ty]
| term t => term t[r:Term]


instance instRenMap_SpineElem : RenMap SpineElem where
  rmap := SpineElem.rmap

@[simp]
def SpineElem.Ty.smap (σ : Subst Ty) : SpineElem -> SpineElem
| type T => type T[σ]
| term t => term t[σ:Ty]

instance instSubstMap_SpineElemTy : SubstMap SpineElem Ty where
  smap := SpineElem.Ty.smap

@[simp]
theorem SpineElem.Ty.subst_type : (type T)[σ:Ty] = type T[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem SpineElem.Ty.subst_term : (term T)[σ:Ty] = term T[σ:_] := by
  simp [SubstMap.smap]

@[simp]
def SpineElem.Term.smap (σ : Subst Term) : SpineElem -> SpineElem
| type T => type T
| term t => term t[σ]

instance instSubstMap_SpineElemTerm : SubstMap SpineElem Term where
  smap := SpineElem.Term.smap

@[simp]
theorem SpineElem.Term.subst_type : (type T)[σ:Term] = type T := by
  simp [SubstMap.smap]

@[simp]
theorem SpineElem.Term.subst_term : (term T)[σ:Term] = term T[σ:_] := by
  simp [SubstMap.smap]

def SpineElem.beq : SpineElem -> SpineElem -> Bool
| .type A, .type B => A == B
| .term a, .term b => a == b
| _, _ => false


def SpineElem.size : SpineElem -> Nat
| .type _ => 0
| .term a => a.size

def Term.spine : Term -> Option (String × List SpineElem)
| .global x => return (x, [])
| .app f a => do
  let (x, sp) <- spine f
  (x, sp ++ [.term a])
| f `•[a] => do
  let (x, sp) <- spine f
  (x, sp ++ [.type a])
| _ => none

def Term.apply (t : Term) : List SpineElem -> Term
| [] => t
| .cons (.type A) tl => (t `•[A]).apply tl
| .cons (.term a) tl => (t `• a).apply tl

def Spine.to_subst : List SpineElem -> IteratedSubst
| [] => .nil
| .cons (.term t) tl => .term (su t::+0) (Spine.to_subst tl)
-- | .cons (.oterm t) tl => .term (su t::+0) (Spine.to_subst tl)
| .cons (.type t) tl => .type (su t::+0) (Spine.to_subst tl)

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
    case type hd => apply @ih (t `•[hd])
    case term hd => apply @ih (t `• hd)
    -- case oterm hd => apply @ih (t ∘[hd])

macro "SurfaceSpine_app_eq_solve" x:term : tactic => `(tactic| {
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
  (f `• a).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [.term a] ∧ f.spine = some (x, sp')
:= by SurfaceSpine_app_eq_solve x

@[simp]
theorem Spine.appt_eq {f : Term} :
  (f `•[a]).spine = some (x, sp)
  <-> ∃ sp', sp = sp' ++ [.type a] ∧ f.spine = some (x, sp')
:= by SurfaceSpine_app_eq_solve x

macro "SurfaceSpine_apply_solve" sp:Lean.Parser.Tactic.elimTarget "," t:term : tactic => `(tactic| {
  induction $sp generalizing $t <;> simp [Term.apply]
  case cons hd tl ih _ =>
  cases hd <;> simp [Term.apply]
  all_goals rw [ih]
})

theorem Spine.apply_term {t : Term} : t.apply sp `• a = t.apply (sp ++ [.term a]) := by
  SurfaceSpine_apply_solve sp, t

-- theorem Spine.apply_oterm {t : Term} : t.apply sp ∘[a] = t.apply (sp ++ [.oterm a]) := by
--   spine_apply_solve sp, t

theorem Spine.apply_type {t : Term} : t.apply sp `•[a] = t.apply (sp ++ [.type a]) := by
  SurfaceSpine_apply_solve sp, t

macro "SurfaceSpine_apply_eq_case_solve"
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
  : t.spine = some (x, sp) -> t = (g`#x).apply sp
:= by
  intro h
  fun_induction Term.spine generalizing x sp <;> simp at *
  case _ y =>
    rcases h with ⟨e1, e2⟩; subst e1 e2
    simp [Term.apply]
  case _ ih => SurfaceSpine_apply_eq_case_solve h, ih, apply_term
--  case _ ih => spine_apply_eq_case_solve h, ih, apply_oterm
  case _ ih => SurfaceSpine_apply_eq_case_solve h, ih, apply_type

theorem Spine.apply_compose {t : Term}
  : t.spine = some (x, sp1) -> (t.apply sp2).spine = some (x, sp1 ++ sp2)
:= by
  intro h; induction sp2 generalizing t x sp1
  simp [Term.apply]; exact h
  case _ hd tl ih =>
  cases hd <;> simp [Term.apply] at *
  case _ T =>
    have lem : (t `•[T]).spine = some (x, sp1 ++ [.type T]) := by simp; exact h
    replace ih := ih lem; simp at ih; exact ih
  case _ a =>
    have lem : (t `• a).spine = some (x, sp1 ++ [.term a]) := by simp; exact h
    replace ih := ih lem; simp at ih; exact ih
  -- case _ a =>
  --   have lem : (t ∘[a]).spine = some (x, sp1 ++ [.oterm a]) := by simp; exact h
  --   replace ih := ih lem; simp at ih; exact ih

@[simp]
theorem Spine.apply_eta : ((g`#x).apply sp).spine = some (x, sp) := by
  have lem := @apply_compose x [] sp g`#x (by simp [Term.spine])
  simp at lem; exact lem

theorem Spine.apply_spine_compose {t : Term}:
  t.apply (s1 ++ s2) = (t.apply s1).apply s2 := by
induction t, s1 using Term.apply.induct generalizing s2 <;> simp [Term.apply] at *
all_goals (case _ ih => apply ih)

theorem Spine.term_spine_extension_exists {t : Term} {x} {a} {sp} :
t.spine = some (x, sp ++ [.term a]) -> ∃ t', t = t' `• a := by
intro h
replace h := Spine.apply_eq h
rw[Spine.apply_spine_compose] at h; simp [Term.apply] at h
exists (g`#x).apply sp;

theorem Spine.type_spine_extension_exists {t : Term} {x} {a} {sp} :
t.spine = some (x, sp ++ [.type a]) -> ∃ t', t = t' `•[ a ] ∧ t' = (g`#x).apply sp := by
intro h
replace h := Spine.apply_eq h
rw[Spine.apply_spine_compose] at h; simp [Term.apply] at h
exists (g`#x).apply sp;

theorem Spine.size_atleast_one {t : Term} {x} {sp}:
  t.spine = some (x, sp) -> t.size ≥ 1
:= by
induction sp using List.reverse_ind generalizing t x
case _ =>
  intro h1
  replace h1 := Spine.apply_eq h1
  simp [Term.apply] at h1; subst t; simp
case _ hd tl ih =>
  intro h1
  cases hd
  case term =>
    replace h1 := Spine.term_spine_extension_exists h1
    rcases h1 with ⟨f, h1a, h2a⟩;
    simp
  case type =>
    replace h1 := Spine.type_spine_extension_exists h1
    rcases h1 with ⟨f, h1a, h2a⟩;
    subst t; simp

theorem Spine.elem_size_le_term {t : Term} :
  t.spine = some (x, sp) ->
  ∀ e, e ∈ sp -> e.size < t.size
 := by
  intro h1 e h2
  cases e <;> simp [SpineElem.size]
  case type e =>
    replace h1 := Spine.size_atleast_one h1; omega
  case term e =>
  induction t using Term.spine.induct generalizing x sp <;> simp [Term.spine] at h1
  case _ => cases h1.1; cases h1.2; simp at h2
  case _ ih =>
    rw[Option.bind_eq_some_iff] at h1
    rcases h1 with ⟨sp', h1a, h1b⟩
    cases h1b
    simp; replace ih := ih h1a
    cases sp'; case _ sp' =>
    revert sp'; intro sp; case _ f a _ =>
    induction sp using List.reverse_ind generalizing f a
    case _ =>
      simp at *; intro h1a e; cases e; omega;
    case _ hd tl ih =>
      cases hd
      case term =>
        intro h1 h2 h3; simp at *
        replace h1 := Spine.term_spine_extension_exists h1
        rcases h1 with ⟨f, h1a, h2a⟩;
        cases h2;
        case _ h2 => replace h3 := h3 (Or.inl h2); omega
        case _ h2 =>
             cases h2;
             case _ h2 => replace h3 := h3 (Or.inr h2); omega
             case _ h2 => subst h2; omega
      case type =>
        intro h1 h2 h3; simp at *
        replace h1 := Spine.type_spine_extension_exists h1
        rcases h1 with ⟨f, h1a, h2a⟩;
        cases h2;
        case _ h2 => replace h3 := h3 h2; omega
        case _ h2 =>
             cases h2;
             case _ h2 => omega
  case _ ih =>
    rw[Option.bind_eq_some_iff] at h1
    rcases h1 with ⟨sp', h1a, h1b⟩
    cases h1b
    simp; replace ih := ih h1a
    cases sp'; case _ sp' =>
    revert sp'; intro sp; case _ f a _ =>
    simp;
    intro h1 h2 ih; replace ih := ih h2; omega

end Surface

import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Term.Variant
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Inversion
import SystemFD.Metatheory.Weaken
import SystemFD.Metatheory.Substitution
import SystemFD.Metatheory.Uniqueness
import SystemFD.Metatheory.Classification
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Progress
import SystemFD.Metatheory.Determined

def ExistsUnique {α : Sort u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

def Trace := List Nat

inductive InstanceTrace : Ctx Term -> Term -> Trace -> Prop where
| body {b : Term} :
  b.Determined Γ.variants ->
  InstanceTrace Γ b []
| lam :
  InstanceTrace (.type A::Γ) t tr ->
  InstanceTrace Γ (`λ[A] t) tr
| lamt :
  InstanceTrace (.kind A::Γ) t tr ->
  InstanceTrace Γ (Λ[A] t) tr
| guard :
  some (x, sp) = p.neutral_form ->
  InstanceTrace Γ c tr ->
  InstanceTrace Γ (.guard p s c) (x::tr)

inductive TraceType : Ctx Term -> Term -> Trace -> Prop where
| head :
  some (x, sp) = t.neutral_form ->
  TraceType Γ t []
| arrow1 {Γ : Ctx Term} :
  (none = A.neutral_form
    ∨ (∀ x sp, some (x, sp) = A.neutral_form -> ¬ Γ.is_opent x)) ->
  TraceType (.empty::Γ) B tr ->
  TraceType Γ (A -t> B) tr
| arrow2  {Γ : Ctx Term} :
  some (x, sp) = A.neutral_form ->
  Γ.is_opent x ->
  TraceType (.empty::Γ) B tr ->
  TraceType Γ (A -t> B) (x::tr)
| all :
  TraceType (.kind A::Γ) B tr ->
  TraceType Γ (∀[A] B) tr

def trace_set : Trace -> List Trace := sorry

def HasTrace (Γ : Ctx Term) (i : Nat) (tr : Trace) : Prop :=
  ∀ A t,
  Γ d@ i = .inst A t ->
  InstanceTrace Γ t tr

def Trace.Saturated (Γ : Ctx Term) (ts : List Trace) : Prop :=
  ∀ t ∈ ts, ExistsUnique (HasTrace Γ · t)

def Ctx.Saturated (Γ : Ctx Term) : Prop :=
  ∀ i A tr,
  Γ d@ i = .openm A ->
  TraceType Γ A tr ->
  Trace.Saturated Γ (trace_set tr)

theorem Ctx.saturated_implies_determined {Γ : Ctx Term} : Γ.Saturated -> ∀ i, Determined.openm Γ i := by
  intro h i T G sp h1 h2 h3
  have lem1 : some (i, sp) = Term.neutral_form ((#i).apply_spine sp) := by sorry
  have lem2 : some T = (Γ d@ i).get_type := by sorry
  have lem3 : Γ.is_openm i := by sorry
  generalize tldef : get_instances Γ i = tl
  generalize tlpdef : List.map (·.apply_spine sp) tl = tl'
  generalize zdef : List.foldl (·⊕·) `0 tl' = z
  have lem4 : z = `0 ∨ (∃ (t1 t2 : Term), z = (t1 ⊕ t2)) := by sorry
  induction z generalizing tl'
  all_goals simp at lem4
  case zero => sorry
  case ctor2 v t1 t2 ih1 ih2 =>

    sorry
  -- apply Exists.intro _; apply And.intro
  -- apply RedPlus.stepr
  -- apply Red.inst lem1 lem2 h2 lem3 (Eq.symm tldef) (Eq.symm tlpdef) (Eq.symm zdef)

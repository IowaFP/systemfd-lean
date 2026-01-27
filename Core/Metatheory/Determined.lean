import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

open LeanSubst

def Term.Determined (t : Term) : Prop :=
  VariantMissing [.ctor2 .choice, .ctor0 .zero, .guard] t

def Determined.openm (G : List Global) (x : String) : Prop :=
  ∀ Δ Γ T sp,
    lookup x G = some (.openm x T) ->
    sp.length ≥ T.arity ->
    SpineType x G Δ Γ sp T ->
    ∃ t, Plus (Red G) ((g#x).apply sp) t ∧ Term.Determined t

def Determined.defn (G : List Global) (x : String) : Prop :=
  ∀ T t,
    lookup x G = some (.defn x T t) ->
    Term.Determined t

def Global.Determined (G : List Global) : Prop :=
  ∀ x, Determined.openm G x ∧ Determined.defn G x

theorem determined_progress :
  G&[],[] ⊢ t : A ->
  t.Determined ->
  Global.Determined G ->
  Value G t ∨ (∃ t', Plus (Red G) t t' ∧ t'.Determined)
:= by
  sorry

-- Syntactic approximation of determined
def ExistsUnique {α : Sort u} (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

def Trace : Type := List String

inductive InstTrace (G : List Global) : Term -> Trace -> Prop where
| body : t.Determined -> InstTrace t []
| lam_open :
  A.spine = some (x, sp) ->
  InstTrace t tr ->
  InstTrace (λ[A] t) tr
| lam_closed :
  InstTrace t tr ->
  InstTrace (λ[A] t) tr
| guard :
  InstTrace c tr ->
  InstTrace (.guard p s c) tr

inductive SpineTrace : List SpineElem -> Trace -> Prop where
| nil : SpineTrace [] []
| type : SpineTrace tl tr -> SpineTrace (.type a :: tl) tr
| term :
  a.Determined ->
  SpineTrace tl tr ->
  SpineTrace (.term a :: tl) tr
| oterm :
  a.Determined ->
  a.spine = some (x, sp) ->
  SpineTrace tl tr ->
  SpineTrace (.oterm a :: tl) (x::tr)

def Saturated (G : List Global) : Prop :=
  ∀ x insts,
  instances x G = insts ->
  sorry

theorem inst_red_trace_agree :
  InstTrace t tr ->
  SpineTrace sp tr ->
  G&Δ,Γ ⊢ t.apply sp : T ->
  ∃ t', Star (Red G) (t.apply sp) t' ∧ t'.Determined
:= by
  intro h1 h2 j
  induction h1 generalizing sp G Δ Γ T
  case body => sorry
  case lam t tr b A h1 ih =>
    cases sp
    case _ => sorry
    case _ hd sp =>
      cases hd
      case type B =>
        sorry
      case term a =>
        sorry
      case oterm a =>
        simp [Term.apply] at *
        have lem : b = b◯ := sorry -- learned from j
        subst lem
        cases h2; case _ x' sp' tr' q1 q2 h2 =>

        sorry
  case guard =>
    sorry

theorem inst_red_trace_disagree :
  InstTrace t tr1 ->
  SpineTrace sp tr2 ->
  tr1 ≠ tr2 ->
  Star (Red G) (t.apply sp) `0
:= by
  sorry

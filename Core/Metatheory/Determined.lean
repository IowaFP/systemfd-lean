import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

open LeanSubst

def Term.Determined (t : Term) : Prop :=
  VariantMissing [.ctor2 .choice, .ctor0 .zero, .guard] t

def SpineElem.Determined : SpineElem -> Prop
| type _ => True
| term t => t.Determined
| oterm t => t.Determined

def Determined.openm (G : List Global) (x : String) : Prop :=
  ∀ Δ Γ T sp,
    lookup x G = some (.openm x T) ->
    sp.length ≥ T.arity ->
    SpineType g#x G Δ Γ sp T ->
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
| base :
  t.Determined ->
  InstTrace G t []
| lam :
  InstTrace G t tr ->
  InstTrace G (λ[A] t) tr
| tlam :
  InstTrace G t tr ->
  InstTrace G (Λ[K] t) tr
| guard_inner :
  p.spine = some (d, sp) ->
  InstTrace G t tr ->
  InstTrace G (.guard p #x t) (d::tr)
| guard_outer :
  p.spine = some (d, sp1) ->
  s.spine = some (y, sp2) ->
  InstTrace G t tr ->
  InstTrace G (.guard p s t) tr



-- inductive InstTrace (G : List Global) : Term -> Trace -> Prop where
-- | body : t.Determined -> InstTrace G t []
-- | lam_open :
--   A.spine = some (x, sp) ->
--   is_opent G x ->
--   InstTrace G t tr ->
--   InstTrace G (λ[A] t) tr
-- | lam_closed :
--   (A.spine = none ∨ (∃ x sp, A.spine = some (x, sp) ∧ ¬ is_opent G x)) ->
--   InstTrace G t tr ->
--   InstTrace G (λ[A] t) tr
-- | guard :
--   InstTrace G c tr ->
--   InstTrace G (.guard p s c) tr

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
  InstTrace G t tr ->
  SpineTrace sp tr ->
  sp.length ≥ B.arity ->
  G&[],[] ⊢ t : B ->
  G&[],[] ⊢ t.apply sp : T ->
  ∃ t', Star (Red G) (t.apply sp) t' ∧ t'.Determined
:= by
  intro j1 j2 h j3 j4
  induction j2 generalizing t B T
  case nil => sorry
  case term => sorry
  case oterm x sp tl tr a q1 q2 j ih =>
    cases j1
    case lam => sorry
    case tlam => sorry -- impossible
    case guard_inner => sorry -- impossible
    case guard_outer d sp1 y sp2 t p s q3 q4 j1 =>

      sorry
  case type tl tr A j ih =>
    cases j1
    case base j1 => sorry -- already determined
    case lam => sorry -- impossible
    case tlam t K j1 =>
      simp [Term.apply] at *
      sorry
    case guard_inner => sorry -- impossible
    case guard_outer d sp1 y sp2 t p s q1 q2 j1 =>

      sorry

-- theorem inst_red_trace_disagree :
--   InstTrace t tr1 ->
--   SpineTrace sp tr2 ->
--   tr1 ≠ tr2 ->
--   Star (Red G) (t.apply sp) `0
-- := by
--   sorry

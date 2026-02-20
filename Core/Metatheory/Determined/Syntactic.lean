import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Metatheory.SpineType
import Core.Metatheory.Determined.Semantic

open LeanSubst
namespace Core

@[simp]
abbrev String.rmap (_ : Endo Ren) (_ : Ren) : String -> String := λ x => x

instance : RenMap String where
  rmap := String.rmap

inductive GuardTrace where
| nil : GuardTrace
| bound : String -> List SpineElem -> Nat -> Telescope -> GuardTrace -> GuardTrace
| applied : String -> List SpineElem -> Term -> Telescope -> GuardTrace -> GuardTrace

@[simp]
def GuardTrace.rmap (lf : Endo Ren) (r : Ren) : GuardTrace -> GuardTrace
| nil => nil
| bound x sp n te tr => bound x (sp.map (·[r:Term])) (r n) te (rmap lf (tele_lift_ren te r) tr)
| applied x sp t te tr => applied x (sp.map (·[r:Term])) t[r:Term] te (rmap lf (tele_lift_ren te r) tr)

instance : RenMap GuardTrace where
  rmap := GuardTrace.rmap

@[simp]
def GuardTrace.from_act (a : Subst.Action Term) (x : String) (sp : List SpineElem) (te : Telescope) (tr : GuardTrace) : GuardTrace :=
  match a with
  | re k => bound x sp k te tr
  | su y => applied x sp y te tr

@[simp]
def GuardTrace.smap (lf : Endo (Subst Term)) (σ : Subst Term) : GuardTrace -> GuardTrace
| nil => nil
| bound x sp n te tr => from_act (σ n) x (sp.map (·[σ:Term])) te (smap lf (tele_lift te σ) tr)
| applied x sp t te tr => applied x (sp.map (·[σ:Term])) t[σ] te (smap lf (tele_lift te σ) tr)

instance : SubstMap GuardTrace Term where
  smap := GuardTrace.smap

@[simp]
theorem GuardTrace.subst_nil :
  (GuardTrace.nil)[σ:Term] = .nil
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem GuardTrace.subst_bound :
  (GuardTrace.bound x sp n te tr)[σ:Term] = from_act (σ n) x (sp.map (·[σ:Term])) te tr[tele_lift te σ:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem GuardTrace.subst_applied :
  (GuardTrace.applied x sp t te tr)[σ:Term] = .applied x (sp.map (·[σ:Term])) t[σ:_] te tr[tele_lift te σ:_]
:= by simp [Subst.apply, SubstMap.smap]

inductive InstTrace where
| base : GuardTrace -> InstTrace
| lam : InstTrace -> InstTrace
| tlam : InstTrace -> InstTrace

@[simp]
def InstTrace.arity : InstTrace -> Nat
| base _ => 0
| lam tr => tr.arity + 1
| tlam tr => tr.arity + 1

-- @[simp]
-- def InstTraceElem.contains (i : Nat) : InstTraceElem -> Bool
-- | bound _ n => i = n
-- | applied _ _ => false
-- | lam  => false

@[simp]
def InstTrace.rmap (lf : Endo Ren) (r : Ren) : InstTrace -> InstTrace
| base tr => base tr[r:Term]
| lam tr => lam (rmap lf (lf r) tr)
| tlam tr => tlam (rmap lf r tr)

instance : RenMap InstTrace where
  rmap := InstTrace.rmap

@[simp]
def InstTrace.smap (lf : Endo (Subst Term)) (σ : Subst Term) : InstTrace -> InstTrace
| base tr => base tr[σ:Term]
| lam tr => lam (smap lf (lf σ) tr)
| tlam tr => tlam (smap lf σ tr)

instance : SubstMap InstTrace Term where
  smap := InstTrace.smap

@[simp]
theorem InstTrace.subst_nil :
  (InstTrace.base tr)[σ:Term] = .base tr[σ:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_lam :
  (InstTrace.lam tr)[σ:Term] = .lam tr[σ.lift:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_tlam :
  (InstTrace.tlam tr)[σ:Term] = .tlam tr[σ:_]
:= by simp [Subst.apply, SubstMap.smap]

-- def InstTrace.empty : InstTrace := λ _ => none

-- def InstTrace.update (i : Nat) (x : String) (g : InstTrace) : InstTrace
-- | n => if n = i then x else g n

-- def InstTrace.cons (x : String) (g : InstTrace) : InstTrace
-- | 0 => x
-- | n + 1 => g n

-- def InstTrace.skip (g : InstTrace) : InstTrace
-- | 0 => none
-- | n + 1 => g n

-- def Trace : Type := List String

-- def get_guard_pattern (x : Nat) : Term -> Option String
-- | λ[_] t => get_guard_pattern (x + 1) t
-- | Λ[_] t => get_guard_pattern (x + 1) t
-- | .guard p #y t => do
--   let (hd, _) <- p.spine
--   if x = y then hd else get_guard_pattern x t
-- | .guard _ _ t => get_guard_pattern x t
-- | _ => none

-- def OpenValue (G : List Global) (t : Term) : Prop := sorry

-- 1. Need a context of free vars that tracks requirements on the substitution
-- 2. Need a context for outer guards that tracks what trace has been substituted for that guard
-- 3. Seems like you need two separate traces: the open lambda traces and the guard traces
--    as you substitute, the open lambda trace gets propagated into the guard trace

inductive TeleSpineAgree : Telescope -> List SpineElem -> Prop where
| nil : TeleSpineAgree .nil []
| lam :
  TeleSpineAgree te sp ->
  TeleSpineAgree (.ty A te) (.term t :: sp)
| olam :
  TeleSpineAgree te sp ->
  TeleSpineAgree (.ty A te) (.oterm t :: sp)
| tlam :
  TeleSpineAgree te sp ->
  TeleSpineAgree (.kind K te) (.type A :: sp)

theorem TeleSpineAgree.subst_tele (σ : Subst Ty) :
  TeleSpineAgree te sp ->
  TeleSpineAgree te[σ:_] sp
:= by
  intro j; induction j generalizing σ <;> simp
  case nil => apply nil
  case lam ih => apply lam (ih _)
  case olam ih => apply olam (ih _)
  case tlam ih => apply tlam (ih _)

inductive GetGuardTrace (G : List Global) : List Ty -> Term -> GuardTrace -> Prop where
| base :
  t.Determined ->
  GetGuardTrace G Γ t .nil
| guard_bound {Γ : List Ty} :
  Γ[x]? = some A ->
  lookup_type G px = some B ->
  A.spine = some (Ax, spA) ->
  is_opent G Ax ->
  p.spine = some (px, sp) ->
  t.telescope = (te, b) ->
  GetGuardTrace G (te.extend Γ) b tr ->
  GetGuardTrace G Γ (.guard p #x t) (.bound px sp x te tr)
| guard_applied :
  p.spine = some (px, sp1) ->
  s.spine = some (sx, sp2) ->
  t.telescope = (te, b) ->
  (∀ q, prefix_equal sp1 sp2 = some q -> TeleSpineAgree te q) ->
  GetGuardTrace G (te.extend Γ) b tr ->
  GetGuardTrace G Γ (.guard p s t) (.applied px sp1 s te tr)

inductive GuardTraceMatched : GuardTrace -> Prop where
| nil : GuardTraceMatched .nil
| cons :
  s.spine = some (x, sp2) ->
  prefix_equal sp1 sp2 = some q ->
  GuardTraceMatched tr ->
  GuardTraceMatched (.applied x sp1 s te tr)

inductive GuardTraceMissed : GuardTrace -> Prop where
| skip :
  GuardTraceMissed tr ->
  GuardTraceMissed (.applied px sp1 s te tr)
| miss :
  s.spine = some (y, sp2) ->
  x ≠ y ∨ (prefix_equal sp1 sp2 = none) ->
  GuardTraceMissed (.applied px sp1 s te tr)

@[simp]
def iter_subst : Telescope -> List SpineElem -> IteratedSubst
| .nil, [] => .nil
| .ty _ te, .cons (.oterm a) sp => .term (tele_lift te (su a::+0)) (iter_subst te sp)
| .ty _ te, .cons (.term a) sp => .term (tele_lift te (su a::+0)) (iter_subst te sp)
| .kind _ te, .cons (.type a) sp => .type (tele_lift_ty te (su a::+0)) (iter_subst te[su a::+0:_] sp)
| _, _ => .nil

theorem telescope_iterated_apply {b : Term} :
  TeleSpineAgree te sp ->
  Star (Red G) ((b.tele_intro te).apply sp) (b.isubst (iter_subst te sp))
:= by
  intro j
  induction sp generalizing te b
  case nil =>
    cases j; simp [Term.apply, Term.tele_intro, Term.isubst]
    apply Star.refl
  case cons hd sp ih =>
    cases j
    case lam j =>
      apply Star.stepr
      apply Red.spine_congr_step Red.beta
      simp; apply ih j
    case olam j =>
      apply Star.stepr
      apply Red.spine_congr_step Red.beta
      simp; apply ih j
    case tlam te K A j =>
      simp [Term.tele_intro, Term.apply]
      apply Star.stepr
      apply Red.spine_congr_step Red.betat
      simp; replace ih := @ih te[su A::+0:_] b[tele_lift_ty te (su A::+0):_] (TeleSpineAgree.subst_tele _ j)
      simp [Term.isubst]; apply ih

theorem GetGuardTrace.subst :
  GetGuardTrace G Γ t tr ->
  GetGuardTrace G Γ' t[σ] tr[σ:Term]
:= by
  intro j
  induction j generalizing Γ' σ
  case base => sorry
  case guard_bound x A px B Ax spA sp te b tr p t Γ j1 j2 j3 j4 j5 j6 j7 ih =>
    have lem1 : p[σ:_].spine = some (px, sp.map (·[σ:_])) := Spine.apply_eq_subst σ j5
    have lem2 : t[σ:_].telescope = (te, b[tele_lift te σ]) := by sorry
    simp; generalize zdef : σ x = z at *
    cases z <;> simp
    case re k =>
      apply guard_bound sorry j2 j3 j4 lem1 lem2 ih
    case su s =>
      apply guard_applied lem1 sorry lem2 sorry ih
      sorry; sorry
  case guard_applied px sp1 sx sp2 te b Γ tr p s t j1 j2 j3 j4 j5 ih =>
    have lem1 : p[σ:_].spine = some (px, sp1.map (·[σ:_])) := Spine.apply_eq_subst σ j1
    have lem2 : s[σ:_].spine = some (sx, sp2.map (·[σ:_])) := Spine.apply_eq_subst σ j2
    have lem3 : t[σ:_].telescope = (te, b[tele_lift te σ]) := by sorry
    simp; apply guard_applied lem1 lem2 lem3 sorry ih

theorem GetGuardTrace.matched_reduce :
  GetGuardTrace G Γ t tr ->
  GuardTraceMatched tr ->
  ∃ t', Star (Red G) t t' ∧ t'.Determined
:= by
  intro h1 h2
  induction h1
  case base t j =>
    exists t; apply And.intro Star.refl j
  case guard_bound => cases h2
  case guard_applied px sp1 x sp2 tele b Γ tr p s t j1 j2 j3 j4 j5 ih =>
    cases h2; case _ sp3 q q1 q2 q3 =>
    replace j1 := Spine.apply_eq j1; subst j1
    replace j2 := Spine.apply_eq j2; subst j2
    simp at q2; rcases q2 with ⟨e1, e2⟩; subst e1 e2
    replace q1 := prefix_equal_law q1; subst q1
    replace j3 := Term.telescope_eq_law j3; subst j3
    replace j4 := j4 q sorry
    obtain ⟨b', ih1, ih2⟩ := ih q3
    apply Exists.intro _; apply And.intro
    apply Star.stepr
    apply Red.guard_matched (x := x) (sp := sp1) (sp' := sp1 ++ q) (q := q)
    simp; simp; sorry
    apply telescope_iterated_apply j4
    sorry
  -- induction h2 generalizing t
  -- case nil =>
  --   sorry
  -- case cons x sp2 sp1 q tr s j1 j2 j3 ih =>
  --   cases h1; case _ B sx sp3 tele b k p t q1 q2 q3 q4 q5 q6 q7 =>

  --   sorry

inductive GetInstTrace (G : List Global) : List Ty -> Term -> InstTrace -> Prop where
| base :
  GetGuardTrace G Γ t tr ->
  GetInstTrace G Γ t (.base tr)
| lam :
  GetInstTrace G (A::Γ) t tr ->
  GetInstTrace G Γ (λ[A] t) (.lam tr)
| tlam :
  GetInstTrace G Γ t tr ->
  GetInstTrace G Γ (Λ[K] t) (.tlam tr)

inductive SpineTraceElem where
| term : SpineTraceElem
| oterm : String -> SpineTraceElem
| type : SpineTraceElem

abbrev SpineTrace := List SpineTraceElem

inductive GetSpineTrace : List SpineElem -> SpineTrace -> Prop where
| nil : GetSpineTrace [] []
| term :
  GetSpineTrace sp tr ->
  GetSpineTrace (.term a :: sp) (.term :: tr)
| oterm :
  GetSpineTrace sp tr ->
  a.spine = some (x, spa) ->
  GetSpineTrace (.oterm a :: sp) (.oterm x :: tr)
| type :
  GetSpineTrace sp tr ->
  GetSpineTrace (.type A :: sp) (.type :: tr)
end Core

import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing
import Core.Metatheory.SpineType

open LeanSubst

def Term.Determined (t : Term) : Prop :=
  VariantMissing [.ctor2 .choice, .ctor0 .zero, .guard] t

def SpineElem.Determined : SpineElem -> Prop
| type _ => True
| term t => t.Determined
| oterm t => t.Determined

def Determined.openm (G : List Global) (x : String) : Prop := sorry
  -- ∀ Δ Γ T sp,
  --   lookup x G = some (.openm x T) ->
  --   sp.length ≥ T.arity ->
  --   SpineType g#x G Δ Γ sp T ->
  --   ∃ t, Plus (Red G) ((g#x).apply sp) t ∧ Term.Determined t

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

-- @[simp]
-- def get_spine_trace : List SpineElem -> Option SpineTrace
-- | .nil => return []
-- | .cons (.term _) sp => do
--   let sp <- get_spine_trace sp
--   .term :: sp
-- | .cons (.oterm a) sp => do
--   let sp <- get_spine_trace sp
--   let (x, _) <- a.spine
--   .oterm x :: sp
-- | .cons (.type _) sp => do
--   let sp <- get_spine_trace sp
--   .type :: sp

-- theorem get_spine_trace_iff :
--   (∀ (i : Nat) a, sp[i]? = some (.oterm a) -> a.spine.isSome) ->
--   GetSpineTrace sp tr <-> get_spine_trace sp = some tr
-- := by
--   sorry

-- theorem get_spine_trace_wf :
--   (∀ (i : Nat) a, sp[i]? = some (.oterm a) -> a.spine.isSome) ->
--   ∃ tr, get_spine_trace sp = some tr
-- := by
--   sorry

-- inductive AppliedGuardTrace : InstTrace -> SpineTrace -> GuardTrace -> Prop where
-- | base : AppliedGuardTrace (.base tr) sp tr
-- | term :
--   AppliedGuardTrace tr[+1:String] sp gtr ->
--   AppliedGuardTrace (.lam tr) (.term :: sp) gtr
-- | oterm :
--   AppliedGuardTrace tr[su y::+0:_] sp gtr ->
--   AppliedGuardTrace (.lam tr) (.oterm y :: sp) gtr
-- | type :
--   AppliedGuardTrace tr sp gtr ->
--   AppliedGuardTrace (.tlam tr) (.type :: sp) gtr


-- theorem InstTrace.trace_match_reduce :
--   GetInstTrace G Γ t itr ->
--   GetSpineTrace sp str ->
--   AppliedGuardTrace itr str gtr ->
--   G&Δ,Γ ⊢ t.apply sp : T ->
--   ∃ t', Star (Red G) (t.apply sp) t' ∧ t'.Determined
-- := by
--   intro j1 j2 j3 j4
--   induction j3
--   case base gtr str =>
--     cases j1; case _ j1 =>

--     sorry
--   case term => sorry
--   case oterm => sorry
--   case type =>
--     sorry
  -- induction j3 generalizing Δ Γ t sp T
  -- case base str =>
  --   cases j1; case _ j1 =>
  --   sorry
  -- case term tr str' j ih =>
  --   cases j1; case _ A t j1 =>
  --   cases j2; case _ sp a j2 =>
  --   replace j1 : GetInstTrace G Δ Γ t[su a::+0] tr[+1:String] := sorry
  --   replace j5 : G&Δ,Γ ⊢ (t[su a::+0]).apply sp : T := by sorry
  --   simp at j4; replace j4 : str'.length ≥ tr[+1:String].arity := by sorry
  --   obtain ⟨t', ih1, ih2⟩ := ih j1 j2 j4 j5
  --   sorry
  -- case oterm y tr str' j ih =>
  --   cases j1; case _ A t j1 =>
  --   cases j2; case _ sp'' spa a q1 j2 =>
  --   replace j1 : GetInstTrace G Δ Γ t[su a::+0] tr[su y::+0:String] := by sorry
  --   replace j5 : G&Δ,Γ ⊢ (t[su a::+0]).apply sp'' : T := by sorry
  --   simp at j4; replace j4 : str'.length ≥ tr[su y::+0:String].arity := by sorry
  --   obtain ⟨t', ih1, ih2⟩ := ih j1 j2 j4 j5
  --   sorry
  -- case type =>
  --   sorry
  -- case guard tr str' x y j e ih =>
  --   cases j1; case _ sp1 sp2 q t p s q1 q2 q3 q4 j1 =>
  --   obtain ⟨qtr, lem1⟩ := get_spine_trace_wf q2
  --   replace lem1 := get_spine_trace_iff.2 lem1 q2
  --   replace j5 : G&Δ,Γ ⊢ t.apply (q ++ sp) : T := by sorry
  --   replace j2 : GetSpineTrace (q ++ sp) (qtr ++ str') := by sorry
  --   obtain ⟨t', ih1, ih2⟩ := ih j1 j2 j4 j5

  --   sorry

-- theorem InstTrace.trace_miss_reduce :
--   GetInstTrace G Γ t itr ->
--   GetSpineTrace sp str ->
--   ¬ TraceMatch itr str ->
--   str.length ≥ itr.arity ->
--   G&Δ,Γ ⊢ t.apply sp : T ->
--   Star (Red G) (t.apply sp) `0
-- := by
--   intro j1 j2 j3 j4 j5
--   induction j1 generalizing sp str T
--   case base =>
--     exfalso; apply j3; apply TraceMatch.base
--   case lam Δ A Γ t tr j ih =>
--     cases sp
--     case nil => cases j2; simp at j4
--     case cons hd tl =>
--       cases hd <;> simp [Term.apply] at *
--       case type => sorry
--       case term a =>

--         sorry
--       case oterm =>
--         sorry
--   case tlam =>
--     sorry
--   case guard_bound =>
--     sorry
--   case guard_applied =>
--     sorry

-- inductive InstGuardPreamble (G : List Global) : List Kind -> List Ty -> Trace -> Term -> GuardTrace -> Prop where
-- | base :
--   t.Determined ->
--   InstGuardPreamble G Δ Γ [] t .empty
-- | lam :
--   InstGuardPreamble G Δ (A::Γ)  tr t gtr.skip ->
--   InstGuardPreamble G Δ Γ tr (λ[A] t) gtr
-- | tlam :
--   InstGuardPreamble G (K::Δ) Γ tr t gtr ->
--   InstGuardPreamble G Δ Γ tr (Λ[K] t) gtr
-- | guard_bound {Γ : List Ty} :
--   Γ[x]? = some A ->
--   A.spine = some (z, spA) ->
--   is_opent G z ->
--   p.spine = some (y, sp) ->
--   gtr.update x y = gtru ->
--   InstGuardPreamble G Δ Γ tr t gtr ->
--   InstGuardPreamble G Δ Γ tr (.guard p #x t) gtru
-- | guard :
--   s.spine = some (y, sp) ->
--   InstGuardPreamble G Δ Γ tr t gtr ->
--   y::tr = tru ->
--   InstGuardPreamble G Δ Γ tru (.guard p s t) gtr

-- theorem InstTrace.subst {σ : Subst Term} :
--   (∀ i k, σ i = re k -> Γ[i]? = Γ'[k]?) ->
--   (∀ i b, σ i = su b -> b.Determined) ->
--   (∀ i b, σ i = su b -> tr.any (GuardTraceElem.contains i) -> b.spine.isSome) ->
--   InstTrace G Δ Γ t tr ->
--   InstTrace G Δ Γ' t[σ] (tr.map (·[σ:Term]))
-- := by sorry
  -- intro h1 h2 h3 j
  -- induction j generalizing Γ' σ <;> simp
  -- case base =>
  --   sorry
  -- case lam j ih =>
  --   simp at ih
  --   sorry
  -- case tlam j ih =>
  --   sorry
  -- case guard_bound x A Ax spA px sp Δ t tr tru p Γ j1 j2 j3 j4 j5 j6 ih =>
  --   subst j6; simp
  --   have lem1 : p[σ].spine = some (px, sp.map (·[σ:Term])) := by sorry
  --   replace ih := ih h1 h2 (by {
  --     intro i b q1 q2
  --     apply h3 i b q1
  --     simp [*]
  --   })
  --   generalize zdef : σ x = z at *
  --   cases z <;> simp
  --   case re k =>
  --     have lem2 : Γ'[k]? = some A := by sorry
  --     apply guard_bound lem2 j2 j3 lem1 ih rfl
  --   case su b =>
  --     generalize wdef : b.spine = w at *
  --     cases w
  --     case some w =>
  --       rcases w with ⟨y, ysp⟩; simp
  --       apply guard_applied lem1 wdef ih rfl
  --     case none =>
  --       simp; exfalso
  --       replace h3 := h3 _ _ zdef (by simp)
  --       rw [wdef] at h3; simp at h3
  -- case guard_applied px sp1 sx sp2 Δ Γ t tr tru p s j1 j2 j3 j4 ih =>
  --   subst j4; simp
  --   have lem1 : p[σ].spine = some (px, sp1.map (·[σ:Term])) := by sorry
  --   have lem2 : s[σ].spine = some (sx, sp2.map (·[σ:Term])) := by sorry
  --   replace ih := ih h1 h2 h3
  --   apply guard_applied lem1 lem2 ih rfl

-- theorem InstGuardPreamble.subst {σ : Subst Term} :
--   List.Sublist tr tr' ->
--   (∀ i k, σ i = re k -> gtr i = gtr' k ∧ Γ[i]? = Γ'[k]?) ->
--   (∀ i t, σ i = su t -> gtr' i = none ∧ t.Determined) ->
--   InstGuardPreamble G Δ Γ tr t gtr ->
--   InstGuardPreamble G Δ' Γ' tr' t[σ] gtr'
-- := by
--   intro h1 h2 h3 j
--   induction j generalizing σ Γ' Δ' <;> try simp
--   case base =>
--     have lem1 : gtr' = .empty := by sorry
--     have lem2 : tr' = [] := by sorry
--     subst lem1 lem2
--     apply base
--     sorry
--   case lam j ih =>
--     apply lam
--     sorry
--   case tlam j ih =>
--     apply tlam
--     sorry
--   case guard_bound x A z spA y sp gtru Δ tr t gtr p Γ j1 j2 j3 j4 j5 j6 ih =>
--     generalize zdef : σ x = z at *
--     cases z <;> simp
--     case re k =>
--       obtain ⟨q1, q2⟩ := h2 x k zdef
--       have lem1 : p[σ].spine = some (y, sp.map (·[σ:Term])) := by sorry
--       apply guard_bound
--       rw [<-q2]; exact j1
--       apply j2; apply j3
--       apply lem1
--       repeat sorry
--     case su w =>

--       sorry
--   case guard y sp Δ Γ tr t gtr tru p s j1 j2 j3 ih =>
--     have lem1 : s[σ].spine = some (y, sp.map (·[σ:Term])) := by sorry
--     apply guard lem1
--     repeat sorry

-- inductive InstTrace (G : List Global) : List Kind -> List Term -> Trace -> Term -> Trace -> Prop where
-- | base :
--   InstGuardPreamble G Δ Γ sptr t gtr

-- inductive InstTrace (G : List Global) : List (Term -> Prop) -> Term -> Trace -> Prop where
-- | base :
--   InstGuardPreamble sptr t gtr ->
--   InstTrace G [] t []
-- | lam_closed :
--   (A.spine = none ∨ (∃ x sp, A.spine = some (x, sp) ∧ ¬ is_opent G x)) ->
--   InstTrace G (Term.Determined::ξ) t tr ->
--   InstTrace G ξ (λ[A] t) tr
-- | lam_open :
--   A.spine = some (x, sp) ->
--   is_opent G x ->
--   get_guard_pattern 0 t = some d ->
--   InstTrace G (OpenValue G::ξ) t tr ->
--   InstTrace G ξ (λ[A] t) (d::tr)
-- | tlam :
--   InstTrace G ((λ _ => True)::ξ) t tr ->
--   InstTrace G ξ (Λ[K] t) tr

-- theorem InstTrace.subst (σ : Subst Term) :
--   (∀ i, Term.Determined (σ i)) ->
--   InstTrace G ξ t tr ->
--   InstTrace G ξ t[σ] tr
-- := by
--   intro h j
--   induction j generalizing σ
--   case base => sorry
--   case lam_closed => sorry
--   case lam_open j1 j2 j3 j4 ih =>
--     simp; apply lam_open j1 j2 sorry
--     sorry -- by ih
--   case tlam ih =>
--     simp
--     sorry
--   case guard_inner j ih =>
--     simp
--     sorry
--   case guard_outer => sorry


-- inductive SpineTrace : Term -> List SpineElem -> Prop where
-- | nil : t.Determined -> SpineTrace t []
-- | type :
--   SpineTrace b[su a::+0:Ty] tl ->
--   SpineTrace (Λ[K] b) (.type a :: tl)
-- | term :
--   SpineTrace b[su a::+0] tl ->
--   SpineTrace (λ[A] b) (.term a :: tl)
-- | oterm :
--   SpineTrace b[su a::+0] tl ->
--   SpineTrace (λ[A] b) (.oterm a :: tl)
-- | guard_matched :
--   p.spine = some (x, sp1) ->
--   s.spine = some (x, sp2) ->
--   SpineTrace (.guard p s t) tl
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

-- inductive SpineTrace : List SpineElem -> Trace -> Prop where
-- | nil : SpineTrace [] []
-- | type : SpineTrace tl tr -> SpineTrace (.type a :: tl) tr
-- | term :
--   a.Determined ->
--   SpineTrace tl tr ->
--   SpineTrace (.term a :: tl) tr
-- | oterm :
--   a.Determined ->
--   a.spine = some (x, sp) ->
--   SpineTrace tl tr ->
--   SpineTrace (.oterm a :: tl) (x::tr)

-- def Saturated (G : List Global) : Prop :=
--   ∀ x insts,
--   instances x G = insts ->
--   sorry

-- theorem inst_red_trace_agree :
--   InstTrace G t tr ->
--   SpineTrace sp tr ->
--   sp.length ≥ B.arity ->
--   G&[],[] ⊢ t : B ->
--   G&[],[] ⊢ t.apply sp : T ->
--   ∃ t', Star (Red G) (t.apply sp) t' ∧ t'.Determined
-- := by
--   intro j1 j2 h j3 j4
--   induction j2 generalizing t B T
--   case nil => sorry
--   case term => sorry
--   case oterm x sp tl tr a q1 q2 j ih =>
--     cases j1
--     case lam => sorry
--     case tlam => sorry -- impossible
--     case guard_inner => sorry -- impossible
--     case guard_outer d sp1 y sp2 t p s q3 q4 j1 =>

--       sorry
--   case type tl tr A j ih =>
--     cases j1
--     case base j1 => sorry -- already determined
--     case lam => sorry -- impossible
--     case tlam t K j1 =>
--       simp [Term.apply] at *
--       sorry
--     case guard_inner => sorry -- impossible
--     case guard_outer d sp1 y sp2 t p s q1 q2 j1 =>

--       sorry

-- theorem inst_red_trace_disagree :
--   InstTrace t tr1 ->
--   SpineTrace sp tr2 ->
--   tr1 ≠ tr2 ->
--   Star (Red G) (t.apply sp) `0
-- := by
--   sorry

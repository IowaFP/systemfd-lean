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

inductive InstTrace where
| nil : InstTrace
| bound : String -> Nat -> InstTrace -> InstTrace
| applied : String -> String -> InstTrace -> InstTrace
| lam : InstTrace -> InstTrace
| tlam : InstTrace -> InstTrace

inductive InstTraceElem where
| bound : String -> Nat -> InstTraceElem
| applied : String -> String -> InstTraceElem
| lam : InstTraceElem

-- @[simp]
-- def InstTraceElem.contains (i : Nat) : InstTraceElem -> Bool
-- | bound _ n => i = n
-- | applied _ _ => false
-- | lam  => false

@[simp]
def InstTrace.rmap (lf : Endo Ren) (r : Ren) : InstTrace -> InstTrace
| nil => nil
| bound x n tr => bound x (r n) (rmap lf r tr)
| applied x y tr => applied x y (rmap lf r tr)
| lam tr => lam (rmap lf (lf r) tr)
| tlam tr => tlam (rmap lf r tr)

instance : RenMap InstTrace where
  rmap := InstTrace.rmap

@[simp]
def InstTrace.from_act (x : String) (a : Subst.Action String) (tr : InstTrace) : InstTrace :=
  match a with
  | re k => bound x k tr
  | su y => applied x y tr

@[simp]
def InstTrace.smap (lf : Endo (Subst String)) (σ : Subst String) : InstTrace -> InstTrace
| nil => nil
| bound x n tr => from_act x (σ n) (smap lf σ tr)
| applied x y tr => applied x y (smap lf σ tr)
| lam tr => lam (smap lf (lf σ) tr)
| tlam tr => tlam (smap lf σ tr)

instance : SubstMap InstTrace String where
  smap := InstTrace.smap

@[simp]
theorem InstTrace.subst_nil :
  (InstTrace.nil)[σ:String] = .nil
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_bound :
  (InstTrace.bound x n tr)[σ:String] = from_act x (σ n) tr[σ:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_applied :
  (InstTrace.applied x y tr)[σ:String] = .applied x y tr[σ:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_lam :
  (InstTrace.lam tr)[σ:String] = .lam tr[σ.lift:_]
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem InstTrace.subst_tlam :
  (InstTrace.tlam tr)[σ:String] = .tlam tr[σ:_]
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

inductive GetInstTrace (G : List Global) : List Kind -> List Ty -> Term -> InstTrace -> Prop where
| base :
  t.Determined ->
  GetInstTrace G Δ Γ t .nil
| lam :
  GetInstTrace G Δ (A::Γ) t tr ->
  GetInstTrace G Δ Γ (λ[A] t) (.lam tr)
| tlam :
  GetInstTrace G (K::Δ) Γ t tr ->
  GetInstTrace G Δ Γ (Λ[K] t) (.tlam tr)
| guard_bound {Γ : List Ty} :
  Γ[x]? = some A ->
  A.spine = some (Ax, spA) ->
  is_opent G Ax ->
  p.spine = some (px, sp) ->
  GetInstTrace G Δ Γ t tr ->
  GetInstTrace G Δ Γ (.guard p #x t) (.bound px x tr)
| guard_applied :
  p.spine = some (px, sp1) ->
  s.spine = some (sx, sp2) ->
  GetInstTrace G Δ Γ t tr ->
  GetInstTrace G Δ Γ (.guard p s t) (.applied px sx tr)

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

inductive TraceMatch : InstTrace -> SpineTrace -> Prop where
| base : TraceMatch .nil sp
| term :
  TraceMatch tr[+1:String] sp ->
  TraceMatch (.lam tr) (.term :: sp)
| oterm :
  TraceMatch tr[su y::+0:_] sp ->
  TraceMatch (.lam tr) (.oterm y :: sp)
| type :
  TraceMatch tr sp ->
  TraceMatch (.tlam tr) (.type :: sp)
| guard :
  TraceMatch tr sp ->
  x = y ->
  TraceMatch (.applied x y tr) sp

theorem spine_has_base_type {t : Term} :
  G&Δ,Γ ⊢ t.apply sp : T ->
  ∃ B, G&Δ,Γ ⊢ t.apply sp : B ∧ TypeMatch B T
:= by
  intro j; induction sp generalizing t T <;> simp [Term.apply] at *
  case nil =>
    exists T; apply And.intro j
    apply TypeMatch.refl
  case cons hd tl ih =>
    cases hd
    all_goals apply ih j

theorem lambda_spine_forces_term :
  G&Δ,Γ ⊢ (λ[A]t).apply sp : T ->
  ∃ a, ∃ (sp' : List SpineElem), sp = (.term a :: sp')
:= by
  intro j
  sorry

theorem InstTrace.trace_match_reduce :
  GetInstTrace G Δ Γ t itr ->
  GetSpineTrace sp str ->
  TraceMatch itr str ->
  ∃ t', Star (Red G) (t.apply sp) t' ∧ t'.Determined
:= by
  sorry

theorem InstTrace.trace_miss_reduce :
  GetInstTrace G Δ Γ t itr ->
  GetSpineTrace sp str ->
  ¬ TraceMatch itr str ->
  G&Δ,Γ ⊢ t.apply sp : T ->
  Star (Red G) (t.apply sp) `0
:= by
  intro j1 j2 j3 j4
  induction j1 generalizing sp str T
  case base =>
    exfalso; apply j3; apply TraceMatch.base
  case lam Δ A Γ t tr j ih =>

    sorry
  case tlam =>
    sorry
  case guard_bound =>
    sorry
  case guard_applied =>
    sorry

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

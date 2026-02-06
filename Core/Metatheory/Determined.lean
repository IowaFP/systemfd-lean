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

inductive GuardTraceElem where
| bound : String -> Nat -> GuardTraceElem
| applied : String -> String -> GuardTraceElem

@[simp]
def GuardTraceElem.contains (i : Nat) : GuardTraceElem -> Bool
| bound _ n => i = n
| applied _ _ => false

@[simp]
def GuardTraceElem.rmap (_ : Endo Ren) (r : Ren) : GuardTraceElem -> GuardTraceElem
| bound x n => bound x (r n)
| applied x y => applied x y

instance : RenMap GuardTraceElem where
  rmap := GuardTraceElem.rmap

@[simp]
def GuardTraceElem.from_act (x : String) (n : Nat) (a : Subst.Action Term) : GuardTraceElem :=
  match a with
  | re k => bound x k
  | su t =>
    match t.spine with
    | some (y, _) => applied x y
    | none => bound x n

@[simp]
def GuardTraceElem.smap (_ : Endo (Subst Term)) (σ : Subst Term) : GuardTraceElem -> GuardTraceElem
| bound x n => from_act x n (σ n)
| applied x y => applied x y

instance : SubstMap GuardTraceElem Term where
  smap := GuardTraceElem.smap

@[simp]
theorem GuardTraceElem.subst_bound :
  (GuardTraceElem.bound x n)[σ:Term] = from_act x n (σ n)
:= by simp [Subst.apply, SubstMap.smap]

@[simp]
theorem GuardTraceElem.subst_applied :
  (GuardTraceElem.applied x y)[σ:Term] = .applied x y
:= by simp [Subst.apply, SubstMap.smap]

abbrev GuardTrace := List GuardTraceElem

-- def GuardTrace.empty : GuardTrace := λ _ => none

-- def GuardTrace.update (i : Nat) (x : String) (g : GuardTrace) : GuardTrace
-- | n => if n = i then x else g n

-- def GuardTrace.cons (x : String) (g : GuardTrace) : GuardTrace
-- | 0 => x
-- | n + 1 => g n

-- def GuardTrace.skip (g : GuardTrace) : GuardTrace
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

inductive InstTrace (G : List Global) : List Kind -> List Ty -> Term -> GuardTrace -> Prop where
| base :
  t.Determined ->
  InstTrace G Δ Γ t []
| lam :
  InstTrace G Δ (A::Γ) t (tr.map (·[+1:Term])) ->
  InstTrace G Δ Γ (λ[A] t) tr
| tlam :
  InstTrace G (K::Δ) Γ t tr ->
  InstTrace G Δ Γ (Λ[K] t) tr
| guard_bound {Γ : List Ty} :
  Γ[x]? = some A ->
  A.spine = some (Ax, spA) ->
  is_opent G Ax ->
  p.spine = some (px, sp) ->
  InstTrace G Δ Γ t tr ->
  (.bound px x)::tr = tru ->
  InstTrace G Δ Γ (.guard p #x t) tru
| guard_applied :
  p.spine = some (px, sp1) ->
  s.spine = some (sx, sp2) ->
  InstTrace G Δ Γ t tr ->
  (.applied px sx)::tr = tru ->
  InstTrace G Δ Γ (.guard p s t) tru

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

theorem InstTrace.subst {σ : Subst Term} :
  (∀ i k, σ i = re k -> Γ[i]? = Γ'[k]?) ->
  (∀ i b, σ i = su b -> b.Determined) ->
  (∀ i b, σ i = su b -> tr.any (GuardTraceElem.contains i) -> b.spine.isSome) ->
  InstTrace G Δ Γ t tr ->
  InstTrace G Δ Γ' t[σ] (tr.map (·[σ:Term]))
:= by
  intro h1 h2 h3 j
  induction j generalizing Γ' σ <;> simp
  case base =>
    sorry
  case lam j ih =>
    simp at ih
    sorry
  case tlam j ih =>
    sorry
  case guard_bound x A Ax spA px sp Δ t tr tru p Γ j1 j2 j3 j4 j5 j6 ih =>
    subst j6; simp
    have lem1 : p[σ].spine = some (px, sp.map (·[σ:Term])) := by sorry
    replace ih := ih h1 h2 (by {
      intro i b q1 q2
      apply h3 i b q1
      simp [*]
    })
    generalize zdef : σ x = z at *
    cases z <;> simp
    case re k =>
      have lem2 : Γ'[k]? = some A := by sorry
      apply guard_bound lem2 j2 j3 lem1 ih rfl
    case su b =>
      generalize wdef : b.spine = w at *
      cases w
      case some w =>
        rcases w with ⟨y, ysp⟩; simp
        apply guard_applied lem1 wdef ih rfl
      case none =>
        simp; exfalso
        replace h3 := h3 _ _ zdef (by simp)
        rw [wdef] at h3; simp at h3
  case guard_applied px sp1 sx sp2 Δ Γ t tr tru p s j1 j2 j3 j4 ih =>
    subst j4; simp
    have lem1 : p[σ].spine = some (px, sp1.map (·[σ:Term])) := by sorry
    have lem2 : s[σ].spine = some (sx, sp2.map (·[σ:Term])) := by sorry
    replace ih := ih h1 h2 h3
    apply guard_applied lem1 lem2 ih rfl

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

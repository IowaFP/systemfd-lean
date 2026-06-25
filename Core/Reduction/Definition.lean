import Core.Util
import Core.Vec
import Core.Global
import Core.Ty
import Core.Term

open Lilac
open LeanSubst

namespace Core

-- def OpenVarVal (G : List Global) (x : String) (sp : List SpineElem) : Prop :=
--   is_openm G x ∧ ∀ T, lookup_type G x = some T -> sp.length < T.arity

inductive Value (G : List Global) : Term -> Prop where
-- | var : Value G #x
| spctor :
  v ≠ .openm ->
  Value G (.spctor v s tys1 tys2 ts)
-- | app : Value G f -> Value G (f •(b) a)
-- | app :
--   t.spine = some (x, sp) ->
--   (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
--   (∀ e ∈ sp, ∀ t, .oterm t = e -> Value G t) ->
--   is_stable G x ∨ OpenVarVal G x sp ->
--   Value G t
| lam : Value G (λ[A] t)
| lamt : Value G (Λ[K] t)
| refl : Value G (refl! A)

@[simp]
def Ctor2Variant.congr1 : Ctor2Variant -> Bool
| app => true
| apptc => true

@[simp]
def Ctor2Variant.congr2 : Ctor2Variant -> Bool
| app => false
| apptc => true

@[simp]
def TyBindVariant.congr : TyBindVariant -> Bool
| lamt => false
| allc => true

inductive Term.IsData (v : DataConst) : Vec Term m -> Vec Constructor m -> Prop where
| nil : Term.IsData v .nil .nil
| cons {t1 : Vec _ m1} {t2 : Vec _ m2} {t3 : Fun.Vec _ n}:
  Term.IsData v ts cs ->
  Term.spctor (.data v) c t1 t2 t3 = t ->
  ⟨c, m1, t1, m2, t2, n, t3.to⟩ = ct ->
  Term.IsData v (t::ts) (ct::cs)

def Constructor.subst_type : Vec Constructor m -> List (Action Ty)
| .nil => []
| .cons ⟨_, _, _, _, As, _, _⟩ v => Constructor.subst_type v ++ As.list.reverse.map su

def Constructor.subst : Vec Constructor m -> List (Action Term)
| .nil => []
| .cons ⟨_, _, _, _, _, _, ts⟩ v => Constructor.subst v ++ ts.list.reverse.map su

-- def Pattern.match_component : Constructor -> (String × List Ty × Nat) -> Option (List $ Subst.Action Term)
-- | ⟨c1, _, _, _, t2⟩, (c2, _) => if c1 == c2 then some $ Vec.map su t2 else none

inductive Pattern.Match : Vec Constructor m -> Pattern m -> Prop
| nil : Pattern.Match .nil .nil
| cons :
  Pattern.Match cs ps ->
  c = ⟨q, m1, As, m2, As2, n, ts⟩ ->
  p = ⟨q, m1, Bs, m2, n⟩ ->
  Pattern.Match (c::cs) (p::ps)

inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red G ((λ[A] b) • t) b[su t::+0σ]
| betat : Red G ((Λ[A] b) •[t]) b[su t::+0σ]
| cast : Red G (.cast R (refl! A) t) t
-- | sym : Red G (sym! (refl! A)) (refl! A)
-- | seq : Red G ((refl! A) `; (refl! A)) (refl! A)
-- | appc : Red G ((refl! A) •c (refl! B)) (refl! (A • B))
| prj_fst_app : Red G (prj[0] refl! (A • B)) (refl! A)
| prj_snd_app : Red G (prj[1] refl! (A • B)) (refl! B)
| prj_fst_arr: Red G (prj[0] refl! (A -:> B)) (refl! A)
| prj_snd_arr : Red G (prj[1] refl! (A -:> B)) (refl! B)
| allc : Red G (∀c[A] refl! B) (refl! (∀[A] B))
| apptc : Red G ((refl! (∀[K] A)) •c[refl! B]) (refl! A[su B::+0σ])
-- | arrowc : Red G ((refl! A) -c> (refl! B)) (refl! (A -:> B))
-- | choice1 : Red G (`0 `+ t) t
-- | choice2 : Red G (t `+ `0) t
----------------------------------------------------------------
---- Data Matching
----------------------------------------------------------------
| data_match {ss : Fun.Vec Term m} {ps : Fun.Vec (Pattern m) n} :
  Term.IsData .cls ss.to ctors ->
  Pattern.Match ctors (ps i) ->
  b' = (bs i)[Constructor.subst_type ctors ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
  Red G (.mtch m n ss ps bs) b'
| openm_match {i : Nat} {ss : Fun.Vec Term m} :
  Term.IsData .opn ss.to ctors ->
  G[i]? = some (.inst x p b) ->
  Pattern.Match ctors p ->
  b' = b[Constructor.subst_type ctors ++ Subst.id Ty][Ts2.list.reverse.map su ++ Ts1.list.reverse.map su ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
  Red G (openm! x Ts1 Ts2 ss) b'
----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
-- | guard_matched :
--   Term.spine p = some (x, sp) ->
--   Term.spine s = some (x, sp') ->
--   prefix_equal sp sp' = some q ->
--   Red G (.guard p s b) (b.apply q)
-- | guard_missed :
--   Term.spine p = some (x, sp) ->
--   Term.spine s = some (x', sp') ->
--   x ≠ x' ∨ prefix_equal sp sp' = none ->
--   Red G (.guard p s b) `0
----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
-- | inst :
--   Term.spine h = some (x, sp) ->
--   is_openm G x ->
--   (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
--   (∀ e ∈ sp, ∀ t, .oterm t = e -> Value G t) ->
--   lookup_type G x = some T ->
--   sp.length ≥ T.arity ->
--   h' = (List.foldl (·`+·) `0 (instances x G)).apply sp ->
--   Red G h h'
----------------------------------------------------------------
---- Global Definitions
----------------------------------------------------------------
| defn :
  lookup_defn G x = some (A, t) ->
  Red G d#x t
----------------------------------------------------------------
---- Congruence Rules
----------------------------------------------------------------
| ctor1_congr :
  Red G t t' ->
  Red G (.ctor1 v t) (.ctor1 v t')
| apptc_congr1 :
  Red G f f' ->
  Red G (f •c[a]) (f' •c[a])
| apptc_congr2 :
  Red G a a' ->
  Red G (f •c[a]) (f •c[a'])
| app_congr :
  Red G f f' ->
  Red G (f • a) (f' • a)
| allc_congr :
  Red G t t' ->
  Red G (∀c[K] t) (∀c[K] t')
| cast_congr :
  Red G c c' ->
  Red G (.cast R c t) (.cast R c' t)
-- | guard_congr :
--   Red G s s' ->
--   Red G (.guard p s b) (.guard p s' b)
| openm_congr {ts : Fun.Vec Term n} i :
  Red G (ts i) (ts' i) ->
  (∀ j ≠ i, ts j = ts' j) ->
  Red G (openm! x Ts1 Ts2 ts) (openm! x Ts1 Ts2 ts')
| match_congr {ss : Fun.Vec Term m} i :
  Red G (ss i) (ss' i) ->
  (∀ j ≠ i, ss j = ss' j) ->
  Red G (.mtch m n ss ps bs) (.mtch m n ss' ps bs)
----------------------------------------------------------------
---- Absorption Rules
----------------------------------------------------------------
-- | ctor1_absorb :
--   Red G (.ctor1 v `0) `0
-- | ctor2_absorb1 :
--   v.congr1 ->
--   Red G (.ctor2 v `0 t2) `0
-- | ctor2_absorb2 :
--   v.congr2 ->
--   Red G (.ctor2 v t1 `0) `0
-- | tbind_absorb :
--   v.congr ->
--   Red G (.tbind v K `0) `0
-- -- | guard_absorb :
-- --   Red G (.guard p `0 b) `0
-- | match_absorb {ss : Fun.Vec Term m} i :
--   ss i = `0 ->
--   Red G (.mtch m n ss ps bs) `0
----------------------------------------------------------------
---- Mapping Rules
----------------------------------------------------------------
-- | ctor1_map :
--   Red G t t' ->
--   Red G (.ctor1 v (c1 `+ c2)) (.ctor1 v c1 `+ .ctor1 v c2)
-- | ctor2_map1 :
--   v.congr1 ->
--   v ≠ .choice ->
--   Red G (.ctor2 v (c1 `+ c2) t2) (.ctor2 v c1 t2 `+ .ctor2 v c2 t2)
-- | ctor2_map2 :
--   v.congr2 ->
--   v ≠ .choice ->
--   Red G (.ctor2 v t1 (c1 `+ c2)) (.ctor2 v t1 c1 `+ .ctor2 v t1 c2)
-- | tbind_map :
--   v.congr ->
--   Red G (.tbind v K (c1 `+ c2)) (.tbind v K c1 `+ .tbind v K c2)
-- | guard_map :
--   Red G (.guard p (c1 `+ c2) b) (.guard p c1 b `+ .guard p c2 b)
-- | match_map :
--   Red G (.match n (c1 `+ c2) ps ts c) (.match n c1 ps ts c `+ .match n c2 ps ts c)

notation:160 G:160 " ⊢ " t:160 " ~> " t':160 => Red G t t'

inductive RedStar (G : GlobalEnv) : Term -> Term -> Prop where
| refl : RedStar G x x
| step : RedStar G x y -> Red G y z -> RedStar G x z

notation:160 G:160 " ⊢ " t:160 " ~>* " t':160 => RedStar G t t'

inductive RedPlus (G : GlobalEnv) : Term -> Term -> Prop where
| one : Red G x y -> RedPlus G x y
| step : RedPlus G x y -> Red G y z -> RedPlus G x z

notation:160 G:160 " ⊢ " t:160 " ~>+ " t':160 => RedPlus G t t'

namespace Core

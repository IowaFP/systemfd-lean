import Core.Util
import Core.Global
import Core.Ty
import Core.Term

open Lilac
open LeanSubst

namespace Core

def OpenVarVal (G : List Global) (x : String) (sp : List SpineElem) : Prop :=
  is_openm G x ∧ ∀ T, lookup_type G x = some T -> sp.length < T.arity

inductive Value (G : List Global) : Term -> Prop where
-- | var : Value G #x
| dctor : Value G (.dctor n s tys ts)
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
| app _ => true
| cast => false
| seq => true
| appc => true
| apptc => true
| arrowc => true
| choice => true

@[simp]
def Ctor2Variant.congr2 : Ctor2Variant -> Bool
| app .closed => false
| app .open => true
| cast => true
| seq => true
| appc => true
| apptc => true
| arrowc => true
| choice => true

@[simp]
def TyBindVariant.congr : TyBindVariant -> Bool
| lamt => false
| allc => true

-- def Sequ.append : List α -> Sequ α -> Sequ α
-- | [], s => s
-- | .cons hd tl, s => hd :: (append tl s)

def Fin.nat? : (n : Nat) -> Nat -> Option (Fin n)
| 0, _ => none
| n + 1, i => some $ Fin.ofNat (n + 1) i

def Constructor.from_scrutinee : Term -> Option Constructor
| .dctor _ c t1 t2 => some (c, t1, (Vec.to_list t2.to))
| _ => none

def Constructor.from_scrutinees (ss : Vec Term m) : Option $ List Constructor :=
  List.mapM Constructor.from_scrutinee (Vec.to_list ss)

def Pattern.match : (Constructor × (String × List Ty × Nat)) -> Option (List $ Subst.Action Term)
| ((c1, _, t2), (c2, _)) => if c1 == c2 then some $ t2.map su else none

def Pattern.parallel_match n (ss : List Constructor) : Pattern m × Nat -> Option (Subst Term × Fin n)
| (p, i) => do
  let ℓ : List (Constructor × (String × List Ty × Nat)) := List.zip ss (Vec.to_list p)
  let σs <- List.mapM Pattern.match ℓ
  let i <- Fin.nat? n i
  let σ := List.foldr Fun.Sequ.cons +0 (List.flatten σs)
  return (σ, i)

inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red G ((λ[A] b) •(s) t) b[su t::+0]
| betat : Red G ((Λ[A] b) •[t]) b[su t::+0:Ty]
| cast : Red G (.cast R (refl! A) t) t
-- | sym : Red G (sym! (refl! A)) (refl! A)
-- | seq : Red G ((refl! A) `; (refl! A)) (refl! A)
-- | appc : Red G ((refl! A) •c (refl! B)) (refl! (A • B))
| prj_fst_app : Red G (prj[0] refl! (A • B)) (refl! A)
| prj_snd_app : Red G (prj[1] refl! (A • B)) (refl! B)
| prj_fst_arr: Red G (prj[0] refl! (A -:> B)) (refl! A)
| prj_snd_arr : Red G (prj[1] refl! (A -:> B)) (refl! B)
| allc : Red G (∀c[A] refl! B) (refl! (∀[A] B))
| apptc : Red G ((refl! (∀[K] A)) •c[refl! B]) (refl! A[su B::+0])
-- | arrowc : Red G ((refl! A) -c> (refl! B)) (refl! (A -:> B))
-- | choice1 : Red G (`0 `+ t) t
-- | choice2 : Red G (t `+ `0) t
----------------------------------------------------------------
---- Data Matching
----------------------------------------------------------------
| data_match {ss : Fun.Vec Term m} {ps : Fun.Vec (Pattern m) n} :
  Constructor.from_scrutinees ss.to = some ctors ->
  List.firstM (Pattern.parallel_match n ctors) (List.zipIdx (Vec.to_list ps.to)) = some (σ, i) ->
  Red G (.mtch m n ss ps bs) (bs i)[σ]
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
  lookup_defn G x = some t ->
  Red G g#x t
----------------------------------------------------------------
---- Congruence Rules
----------------------------------------------------------------
| ctor1_congr :
  Red G t t' ->
  Red G (.ctor1 v t) (.ctor1 v t')
| ctor2_congr1 :
  v.congr1 ->
  Red G t1 t1' ->
  Red G (.ctor2 v t1 t2) (.ctor2 v t1' t2)
| ctor2_congr2 :
  v.congr2 ->
  Red G t2 t2' ->
  Red G (.ctor2 v t1 t2) (.ctor2 v t1 t2')
| tbind_congr :
  v.congr ->
  Red G t t' ->
  Red G (.tbind v K t) (.tbind v K t')
-- | guard_congr :
--   Red G s s' ->
--   Red G (.guard p s b) (.guard p s' b)
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

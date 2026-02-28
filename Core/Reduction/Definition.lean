import LeanSubst
import Core.Util
import Core.Global
import Core.Ty
import Core.Term
import Lilac.Vect

open LeanSubst


namespace Core

def OpenVarVal (G : List Global) (x : String) (sp : List SpineElem) : Prop :=
  is_openm G x ∧ ∀ T, lookup_type G x = some T -> sp.length < T.arity

inductive Value (G : List Global) : Term -> Prop where
| app :
  t.spine = some (x, sp) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> Value G t) ->
  is_stable G x ∨ OpenVarVal G x sp ->
  Value G t
| choice : Value G t1 -> Value G t2 -> Value G (t1 `+ t2)
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

inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red G ((λ[A] b) •(s) t) b[su t::+0]
| betat : Red G ((Λ[A] b) •[t]) b[su t::+0:Ty]
| cast : Red G (t ▹ refl! A) t
| sym : Red G (sym! (refl! A)) (refl! A)
| seq : Red G ((refl! A) `; (refl! A)) (refl! A)
| appc : Red G ((refl! A) •c (refl! B)) (refl! (A • B))
| apptc : Red G ((refl! (∀[K] A)) •c[refl! B]) (refl! A[su B::+0])
| fst : Red G (fst! (refl! (A • B))) (refl! A)
| snd : Red G (snd! (refl! (A • B))) (refl! B)
| allc : Red G (∀c[A] refl! B) (refl! (∀[A] B))
| arrowc : Red G ((refl! A) -c> (refl! B)) (refl! (A -:> B))
| choice1 : Red G (`0 `+ t) t
| choice2 : Red G (t `+ `0) t
----------------------------------------------------------------
---- Data Matching
----------------------------------------------------------------
| data_match {t  : Term}{sp' : List SpineElem}
             (ps : Vect n Term)
             (cs : Vect n Term)
             (ps': Vect n (Option (List SpineElem × Term))) :
  some (s_h, s_sp) = Term.spine s ->
  ps' = (λ x => do
    let (m_h, m_sp) <- x.fst.spine
    if s_h = m_h then
      match prefix_equal m_sp s_sp  with
      | some p => return (p, x.2)
      | none => none
      else none) <$> ps.zip cs ->
  ps'.any.getD ([], c) = (sp', t) ->
  Red G (.match n s ps cs c) (t.apply sp')

----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  Term.spine p = some (x, sp) ->
  Term.spine s = some (x, sp') ->
  prefix_equal sp sp' = some q ->
  Red G (.guard p s b) (b.apply q)
| guard_missed :
  Term.spine p = some (x, sp) ->
  Term.spine s = some (x', sp') ->
  x ≠ x' ∨ prefix_equal sp sp' = none ->
  Red G (.guard p s b) `0
----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
| inst :
  Term.spine h = some (x, sp) ->
  is_openm G x ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
  (∀ e ∈ sp, ∀ t, .oterm t = e -> Value G t) ->
  lookup_type G x = some T ->
  sp.length ≥ T.arity ->
  h' = (List.foldl (·`+·) `0 (instances x G)).apply sp ->
  Red G h h'
----------------------------------------------------------------
---- Global Definitions
----------------------------------------------------------------
| defn :
  Term.spine h = some (x, sp) ->
  lookup_defn G x = some t ->
  Red G h (t.apply sp)
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
| guard_congr :
  Red G s s' ->
  Red G (.guard p s b) (.guard p s' b)
| match_congr :
  Red G s s' ->
  Red G (.match n s ps ts c) (.match n s' ps ts c)
----------------------------------------------------------------
---- Absorption Rules
----------------------------------------------------------------
| ctor1_absorb :
  Red G (.ctor1 v `0) `0
| ctor2_absorb1 :
  v.congr1 ->
  Red G (.ctor2 v `0 t2) `0
| ctor2_absorb2 :
  v.congr2 ->
  Red G (.ctor2 v t1 `0) `0
| tbind_absorb :
  v.congr ->
  Red G (.tbind v K `0) `0
| guard_absorb :
  Red G (.guard p `0 b) `0
| match_absorb :
  Red G (.match n `0 ps ts c) `0
----------------------------------------------------------------
---- Mapping Rules
----------------------------------------------------------------
| ctor1_map :
  Red G t t' ->
  Red G (.ctor1 v (c1 `+ c2)) (.ctor1 v c1 `+ .ctor1 v c2)
| ctor2_map1 :
  v.congr1 ->
  v ≠ .choice ->
  Red G (.ctor2 v (c1 `+ c2) t2) (.ctor2 v c1 t2 `+ .ctor2 v c2 t2)
| ctor2_map2 :
  v.congr2 ->
  v ≠ .choice ->
  Red G (.ctor2 v t1 (c1 `+ c2)) (.ctor2 v t1 c1 `+ .ctor2 v t1 c2)
| tbind_map :
  v.congr ->
  Red G (.tbind v K (c1 `+ c2)) (.tbind v K c1 `+ .tbind v K c2)
| guard_map :
  Red G (.guard p (c1 `+ c2) b) (.guard p c1 b `+ .guard p c2 b)
| match_map :
  Red G (.match n (c1 `+ c2) ps ts c) (.match n c1 ps ts c `+ .match n c2 ps ts c)

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

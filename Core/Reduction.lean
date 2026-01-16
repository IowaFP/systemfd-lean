import LeanSubst
import Core.Util
import Core.Global
import Core.Ty
import Core.Term

open LeanSubst

def OpenVarVal (G : List Global) (x : String) (sp : List SpineElem) : Prop :=
  is_openm G x ∧ ∀ T, some T = lookup_type x G -> sp.length < T.arity

inductive Value (G : List Global) : Term -> Prop where
| app :
  some (x, sp) = t.spine ->
  is_stable G x ∨ OpenVarVal G x sp ->
  Value G t
| choice : Value G t1 -> Value G t2 -> Value G (t1 `+ t2)
| lam : Value G (λ[A] t)
| lamt : Value G (Λ[K] t)
| refl : Value G (refl! A)

def Ctor2Variant.congr1 : Ctor2Variant -> Bool
| app => true
| appo => true
| cast => false
| seq => true
| appc => true
| apptc => true
| arrowc => true
| choice => true

def Ctor2Variant.congr2 : Ctor2Variant -> Bool
| app => false
| appo => false
| cast => true
| seq => true
| appc => true
| apptc => true
| arrowc => true
| choice => true

def TyBindVariant.congr : TyBindVariant -> Bool
| lamt => false
| allc => true

inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red G ((λ[A] b) • t) b[su t::+0]
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
| data_match {i : Fin n} :
  some (x, sp) = Term.spine p ->
  some (x, sp') = Term.spine s ->
  some q = prefix_equal sp sp' ->
  some i = ctor_idx G x ->
  Red G (.match p s cs) ((cs i).apply q)
----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  some (x, sp) = Term.spine p ->
  some (x, sp') = Term.spine s ->
  some q = prefix_equal sp sp' ->
  Red G (.guard p s b) (b.apply q)
| guard_missed :
  some (x, sp) = Term.spine p ->
  some (x', sp') = Term.spine s ->
  x ≠ x' ∨ none = prefix_equal sp sp' ->
  Red G (.guard p s b) `0
----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
| inst :
  some (x, sp) = Term.spine h ->
  is_openm G x ->
  (∀ e ∈ sp, ∀ a, .oterm a = e -> Value G a) ->
  some T = lookup_type x G ->
  sp.length ≥ T.arity ->
  tl = instances x G ->
  tl' = List.map (·.apply sp) tl ->
  h' = List.foldl (·`+·) `0 tl' ->
  Red G h h'
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
  Red G (.match p s ts) (.match p s' ts)
----------------------------------------------------------------
---- Absorption Rules
----------------------------------------------------------------
| ctor1_asborb :
  Red G (.ctor1 v `0) `0
| ctor2_asborb1 :
  v.congr1 ->
  Red G (.ctor2 v `0 t2) `0
| ctor2_asborb2 :
  v.congr2 ->
  Red G (.ctor2 v t1 `0) `0
| tbind_asborb :
  v.congr ->
  Red G (.tbind v K `0) `0
| guard_asborb :
  Red G (.guard p `0 b) `0
| match_asborb :
  Red G (.match p `0 ts) `0
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
  Red G (.match p (c1 `+ c2) ts) (.match p c1 ts `+ .match p c2 ts)

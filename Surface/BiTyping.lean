import Surface.Term
import Surface.Ty

import Surface.Typing

namespace Surface

inductive Mode : Type where
| chk | syn

@[simp]
abbrev BiTypingArgs : Mode -> Type
| .chk => Term × Ty
| .syn => Term

inductive BiTyping (G : GlobalEnv) :  KindEnv -> TyEnv -> (m : Mode) -> (BiTypingArgs m) -> Prop where
| var :
  Γ[x]? = some A ->
  G&Δ ⊢s A : .base b ->
  BiTyping G Δ Γ .syn (`#x)
-- | global :
--   lookup_type G x = some A ->
--   G&Δ ⊢s A : .base b ->
--   BiTyping G Δ Γ .syn g`#x

-- | mtch (CTy : Vect n Ty)
--        (PTy : Vect n Ty)
--        (pats : Vect n Term)
--        (cs : Vect n Term) :
--   BiTyping G Δ Γ syn s ->
--   ValidTyHeadVariable R (is_data G) ->
--   BiTyping G chk Δ Γ c T -> -- catch all term is of type T
--   (∀ i, ValidHeadVariable (pats i) (is_ctor G)) -> -- patterns are of the right shape
--   (∀ i, BiTyping G chk Δ Γ (pats i) (PTy i)) -> -- each pattern has a type
--   (∀ i, StableTypeMatch Δ (PTy i) R) -> -- the pattern type has a return type that matches datatype
--   (∀ i, BiTyping G chk Δ Γ (cs i) (CTy i)) -> -- each case match has a type
--   (∀ i, PrefixTypeMatch Δ (PTy i) (CTy i) T) -> -- patten type and case type
--   BiTyping G Δ Γ chk ((matchˢ! s pats cs c),  T)

-- | appt :
--   BiTyping G syn Δ Γ f (`∀[K] P) ->
--   G&Δ ⊢s a : K ->
--   P' = P[.su a :: +0:Ty] ->
--   BiTyping G chk Δ Γ (f `•[a]) P'

-- | app :
--   G&Δ ⊢s A : `★ ->
--   BiTyping G Δ Γ .syn f ->
--   BiTyping G Δ Γ .chk (a , A) ->
--   BiTyping G Δ Γ chk (f `• a , B)

-- --------------------------------------------------------------------------------------
-- ---- Terms
-- --------------------------------------------------------------------------------------
-- | lam :
--   G&Δ ⊢s A : .base b1 ->
--   BiTyping G inf Δ (A::Γ) t B ->
--   BiTyping G inf Δ Γ (λˢ[A] t) (A `-:> B)
-- | lamt :
--   Kinding G Δ (`∀[K]P) `★ ->
--   BiTyping G inf (K::Δ) (Γ.map (·[+1])) t P ->
--   BiTyping G inf Δ Γ (Λˢ[K] t) (`∀[K] P)

notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " => " => BiTyping G Mode.syn Δ Γ t
notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " <= " A:170 => BiTyping G Mode.chk Δ Γ t A

end Surface

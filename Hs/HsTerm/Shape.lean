import Hs.HsTerm.Definition
import Hs.HsTerm.Substitution
import Hs.HsCtx

namespace HsTerm

  inductive IsKind : HsTerm -> Prop where
  | type : IsKind `★
  | arrow : IsKind A -> IsKind B -> IsKind (A `-k> B)

  -- inductive IsType : HsCtx HsTerm -> HsTerm -> Prop where
  -- | var : IsType Γ `#x
  -- | all : IsKind A -> IsType (.kind A :: Γ) B -> IsType Γ (`∀{A} B)
  -- | arrow : IsType Γ A -> IsType (.empty :: Γ) B -> IsType Γ (A → B)
  -- | farrow : IsType Γ A -> IsType (.empty :: Γ) B -> IsType Γ (A ⇒ B)
  -- | app : IsType Γ A -> IsType Γ B -> IsType Γ (f `•k a)

  inductive IsType : HsTerm -> Prop where
  | var : IsType `#x
  | all : IsKind A -> IsType B -> IsType (`∀{A} B)
  | arrow : IsType A -> IsType B -> IsType (A → B)
  | farrow : IsType A -> IsType B -> IsType (A ⇒ B)
  | app : IsType A -> IsType B -> IsType (f `•k a)

end HsTerm

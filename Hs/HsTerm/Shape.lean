import Hs.HsTerm.Definition
import Hs.HsTerm.Substitution
import Hs.HsCtx

namespace HsTerm

  inductive IsKind : HsTerm -> Prop where
  | type : IsKind `★
  | arrow : IsKind A -> IsKind B -> IsKind (A `-k> B)

  inductive IsType : HsTerm -> Prop where
  | var : IsType `#x
  | all : IsKind A -> IsType B -> IsType (`∀{A} B)
  | arrow : IsType A -> IsType B -> IsType (A → B)
  | farrow : IsType A -> IsType B -> IsType (A ⇒ B)
  | app : IsType A -> IsType B -> IsType (f `•k a)

end HsTerm

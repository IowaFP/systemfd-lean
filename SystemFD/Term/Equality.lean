import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition

namespace Term
  @[simp]
  def beq : Term -> Term -> Bool
  | _, _ => sorry
end Term

@[simp]
instance BEq_Term : BEq Term where
  beq := Term.beq

@[simp]
instance LawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := sorry
  rfl := sorry

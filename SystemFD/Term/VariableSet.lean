import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition

namespace List
  @[simp]
  def inter [BEq T] (l1 l2 : List T) : List T := filter (elem · l2) l1
end List

namespace Term
  @[simp]
  def vars : Term -> List Nat
  | var x => [x]
  | kind => []
  | type => []
  | ctor1 _ t => vars t
  | ctor2 _ t1 t2 => vars t1 ++ vars t2
  | bind2 _ t1 t2 => vars t1 ++ vars t2
  | ite t1 t2 t3 t4 => vars t1 ++ vars t2 ++ vars t3 ++ vars t4
  | guard t1 t2 t3 => vars t1 ++ vars t2 ++ vars t3
  | letdata t1 t2 => vars t1 ++ vars t2
  | letterm t1 t2 t3 => vars t1 ++ vars t2 ++ vars t3
  | inst _ t1 t2 => vars t1 ++ vars t2
  | decl t => vars t
end Term

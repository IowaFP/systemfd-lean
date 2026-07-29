import Core.Term.Definition

namespace Core.Term

def mkApps (d : Term) (tys : List Ty) (ts : List Term) : Term :=
  let d1 := List.foldl (λ f a => f •[a]) d tys
  List.foldl (λ f a => f • a ) d1 ts

end Core.Term

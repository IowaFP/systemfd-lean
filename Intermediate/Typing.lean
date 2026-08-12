import Intermediate.Global
import Core.Ty
import Surface.Term

import Lilac
open Lilac

namespace Intermediate


inductive VecTyping (J : A -> B -> Prop) : Vec A m -> Vec B m -> Prop
| nil : VecTyping J .nil .nil
| cons :
  J a b ->
  VecTyping J as bs ->
  VecTyping J (a::as) (b::bs)

def Query (G : List Global) (c : DataConst) (qs : Vec String m) (Ts : Vec Core.Ty m) : Prop :=
  VecTyping (lookup_ctor? G c · ·) qs Ts

end Intermediate

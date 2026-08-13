import Intermediate.Global
import Core.Ty
import Surface.Term

import Lilac
open Lilac

namespace Intermediate


def Query (G : List Global) (c : DataConst) (qs : Vec String m) (Ts : Vec Core.Ty m) : Prop :=
  VecTyping (lookup_ctor? G c · ·) qs Ts

end Intermediate

import Surface.Global
import Core.Global

import Translation.Ty
import Translation.Term


def Surface.Entry.translate : Surface.Entry -> Core.Entry
| data x K ctors => .data x K.translate ((λ x => (x.1 , x.2.translate)) <$>ctors)
| ctor x i T => .ctor x i T.translate
| opent x K => .opent x K.translate
| openm x T => .openm x T.translate

notation "⟦" e "⟧" => Surface.Entry.translate e

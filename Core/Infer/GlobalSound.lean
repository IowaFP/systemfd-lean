import Core.Infer.KindSound
import Core.Infer.TypeSound
import Core.Infer.Global

import Core.Global


namespace Core

theorem wf_global_sound :
  ⊢ G ->
  Globals.wf_globals G = some () := by
intro wf
induction G <;> simp at *
case cons hdg tlg ih =>
  cases wf; case _ wfg wftlg =>
  replace ih := ih wfg
  cases hdg <;> simp at *
  case data =>
    rw[Option.bind_eq_some_iff]; exists ()
    constructor; assumption
    rw[Option.bind_eq_some_iff];

    sorry
  case opent =>  sorry
  case openm => sorry
  case defn => sorry
  case inst => sorry
  case instty => sorry

end Core

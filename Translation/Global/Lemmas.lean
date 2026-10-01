import Translation.Global
import Surface.Global
import Core.Global
import Surface.Typing
import Intermediate.Typing
import Core.Typing

import Core.Metatheory.Global
import Translation.Term.Lemmas

import Translation.Global.Lemmas.SI
import Translation.Global.Lemmas.IC

import Lilac
open Lilac


namespace Translation

theorem translate_open_exhaustive_sound {G : Surface.GlobalEnv} {G' : Intermediate.GlobalEnv} {G'' : Core.GlobalEnv} (wf : ⊢ G) :
  ⟦ G ⟧ = .ok G' ->
  ⟦ G' ⟧ = .ok G'' ->
  Ω G''
:= by
  intro h1 h2
  have lem : Ω G' := SI.translate_SI_sound wf h1
  have wf' : ⊢ G' := SI.translate_SI_wf_sound wf h1
  have lem2 : Ω G'' := IC.translate_IC_sound wf' lem h2
  apply lem2

#print axioms translate_open_exhaustive_sound


end Translation

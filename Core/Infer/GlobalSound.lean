import Core.Infer.KindSound
import Core.Infer.TypeSound
import Core.Infer.Global

import Core.Global


namespace Core

theorem wf_global_sound :
  GlobalEnv.wf_globals G = some () ->
  ⊢ G
:= by
intro h
fun_induction GlobalEnv.wf_globals <;> simp at *
case _ =>  -- empty
  apply ListGlobalWf.nil

case _ ih => -- ctors
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h
  apply ListGlobalWf.cons
  · sorry
  · apply ih h2

case _ ih =>  -- openm
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h
  apply ListGlobalWf.cons
  · sorry
  · apply ih h2

case _ ih =>  -- octor
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h; rcases h with ⟨e, h⟩
  apply ListGlobalWf.cons
  · apply GlobalWf.octor
    sorry
    apply e
  · apply ih h2

case _ ih => -- defn
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h7, h8, h⟩
  simp at h; rcases h with ⟨e1, h⟩; subst e1
  apply ListGlobalWf.cons
  · apply GlobalWf.defn
    · replace h8 := Kind.base_kind_sound _ h8; subst h5
      replace h6 := infer_kind_sound h6; apply h6
    · replace h4 := infer_type_sound (ih h2) h4; apply h4
    · apply h
  · apply ih h2

case _ ih => -- inst
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  split at h
  · rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h3, h4, h⟩
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h5, h6, h⟩
    simp at h
    apply ListGlobalWf.cons
    · sorry
    · apply ih h2
  · cases h

case _ ih => -- odata
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨h1, h2, h⟩
  simp at h
  apply ListGlobalWf.cons
  · apply GlobalWf.odata h
  · apply ih h2



theorem open_exhaustive_sound {G : GlobalEnv} :
  G.check_open_exhaustive = some () ->
  OpenExhaustive G := by sorry

end Core

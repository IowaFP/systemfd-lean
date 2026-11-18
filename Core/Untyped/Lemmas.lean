import Core.Untyped.Definition

namespace Untyped

theorem lookup_append_weaken_right :
  Untyped.lookup x G1 = some e → Untyped.lookup x (G1++G2) = some e := by
  intro h
  induction G1
  simp[Untyped.lookup] at h
  case _ head tail ih =>
    cases head; simp
    · simp [Untyped.lookup] at h; split at h <;> try simp at h
      case _ e => subst x; simp; apply h
      case _ e =>
        simp [e];
        apply ih h
    case _ m s pm t => 
      simp [Untyped.lookup]
      simp [Untyped.lookup] at h
      exact ih h
    case _=> 
      simp [Untyped.lookup]
      simp [Untyped.lookup] at h
      exact ih h

theorem lookup_singleton_elim :
  Untyped.lookup x [g] = some (.defn y t)
  → x = y
  := by 
  intros h
  unfold Untyped.lookup at h
  split at h
  contradiction
  case _ => sorry
  case _ => sorry

theorem lookup_elim_left (G : List Untyped.Global) :
  Untyped.lookup x G' = none
  → Untyped.lookup x (G'++G) = Untyped.lookup x G
  := by
    intros h
    sorry

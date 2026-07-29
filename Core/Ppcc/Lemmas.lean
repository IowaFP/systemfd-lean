import Core.Ty
import Core.Term
import Core.Typing

import Core.Ppcc.Basic

namespace Core.Ppcc

theorem EqGraph.ask_type_sound {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv} {eG : EqGraph G Δ Γ} {c : Term} {j : G&Δ, Γ ⊢ c : (T1 ~[K]~ T2)}:
  eG.ask G wf Δ Γ K T1 T2 = some ⟨c, j⟩ ->
  G&Δ, Γ ⊢ c : (T1 ~[K]~ T2) :=
  by intro h; apply j




theorem EqGraph.push_preserves_wf {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv}
  {n : Node G Δ} {eG eG' : EqGraph G Δ Γ} (wf : eG.Wf) :
  eG.push n = eG' ->
  eG'.Wf
:= by
  intro h;
  unfold push at h;
  split at h
  subst h; apply wf
  case _ =>
    simp at h; rw[<-h, Wf]
    simp; rw[List.zipIdx_append]; simp; unfold Wf at wf; simp at wf; apply wf


theorem EqGraph.union_equiv_class_count {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv}
  {eG eG' : EqGraph G Δ Γ} {K : Kind}
  {T1 : Ty} {T2 : Ty} {t : Term} {j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)} (inv : eG.equiv_class_count > 0):
  eG.union (wf := wf) K T1 T2 t j = some eG' ->
  eG'.equiv_class_count < eG.equiv_class_count
  := by
  intro h
  unfold EqGraph.union at h; simp at h
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i1, h1, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i2, h2, h⟩
  split at h
  · rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨ip1, pT1, K1, _, _⟩, h3, h⟩
    rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨ip2, pT2, K2, _, _⟩, h4, h⟩
    simp at h
    split at h
    · simp at h;
      rcases h with ⟨ne, h⟩
      split at h <;> simp at h
      · rw[<-h]; simp; omega
      · rcases h with ⟨_, h⟩; rw[<-h]; simp; omega
    · cases h
  · cases h

theorem EqGraph.get_rep_idx_bounded
  {G : GlobalEnv} {wfg : ⊢ G} {Δ : KindEnv} {Γ : TyEnv}
  {K : Kind} {T1 T2 : Ty} {t : Term} {j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)} {eG : EqGraph G Δ Γ} :
  eG.get_rep wfg T1 = some ⟨ip, T2, K, t, j⟩ ->
  ip < eG.nodes.length
:= by
intro h; unfold get_rep at h
simp at h; rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i, h1, h⟩
simp at h; rcases h with ⟨p, h⟩;
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨i1, repT', K, c, j⟩, h2, h⟩
simp at h; rcases h with ⟨h3, h4, h5⟩; rcases h3 with ⟨p, h3⟩
subst h4; apply p

theorem EqGraph.get_rep_sound
  {G : GlobalEnv} {wfg : ⊢ G} {Δ : KindEnv} {Γ : TyEnv}
  {K : Kind} {T1 T2 : Ty} {t : Term} {j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)} {eG : EqGraph G Δ Γ} :
  eG.get_rep wfg T1 = some ⟨ip, T2, K, t, j⟩ ->
  eG.nodes[ip]?.map (·.ty) = some T2 :=  by
intro h
have lem_idx := EqGraph.get_rep_idx_bounded h
simp; exists eG.nodes[ip]; simp;
unfold get_rep at h; simp at h;
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i, h1, h⟩
simp at h; rcases h with ⟨p, h⟩;
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨⟨i1, repT', K, c, j⟩, h2, h⟩
simp at h; rcases h with ⟨h3, e1, e2, e3⟩; subst e1; subst e2; simp at e3;
rcases e3 with ⟨e3, e4⟩; subst e3; simp at e4; rcases e4 with ⟨e4, e5⟩; subst e4
rcases h3 with ⟨p, h3⟩; rcases h3 with ⟨h3, h4⟩; apply h4



theorem EqGraph.union_preserves_wf
  {G : GlobalEnv} {wfg : ⊢ G} {Δ : KindEnv} {Γ : TyEnv}
  {K : Kind} {T1 T2 : Ty} {t : Term} {j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)} {eG eG' : EqGraph G Δ Γ}
  (wf : eG.Wf) :
  eG.union wfg K T1 T2 t j = some eG' ->
  eG'.Wf
:= by
intro h
unfold union at h; simp at h
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i1, h1, h⟩
rw[Option.bind_eq_some_iff] at h; rcases h with ⟨i2, h2, h⟩
split at h
case _ h3 h4 =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨rep_T1, h5, h⟩
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨rep_T2, h6, h⟩
  split at h
  case _ h7 h8 =>
    simp at h; rcases h with ⟨h9, h⟩
    split at h
    case _ h10 => simp at h; simp only [<-h, Wf]; simp; sorry
    sorry
  case _ => cases h
case _ => cases h

end Core.Ppcc

import Core.Term
import Core.Ty
import Core.Global
import Core.Typing
import Core.Metatheory
import Core.Metatheory.Inversion

import Core.Ppcc.Basic
import Core.Infer

open LeanSubst
open Lilac
namespace Core.Synth

inductive SynthTerm (G : GlobalEnv) (Δ : KindEnv) : TyEnv -> Kind -> Ty -> Term -> Prop where
-- Coercions
| refl  :
  G&Δ ⊢ A : K ->
  SynthTerm G Δ Γ K (A ~[K]~ A) (refl! A)
| sym   :
  SynthTerm G Δ Γ K (A ~[K]~ B) c ->
  t = (Term.cast (t#0 ~[K]~ A⟨Ren.succ Ty⟩) c (refl! A)) ->
  SynthTerm G Δ Γ K (B ~[K]~ A) t
| trans :
  SynthTerm G Δ Γ K (A ~[K]~B) c1 ->
  SynthTerm G Δ Γ K (B ~[K]~ C) c2 ->
  t = (Term.cast (A⟨Ren.succ Ty⟩ ~[K]~ t#0) c2 $ Term.cast (A⟨Ren.succ Ty⟩ ~[K]~ t#0) c1 (refl! A)) ->
  SynthTerm G Δ Γ K (A ~[K]~ C) t
| fst_app {K' : Kind}:
  SynthTerm G Δ Γ K ((A1 • B1) ~[K]~ (A2 • B2)) c ->
  SynthTerm G Δ Γ (K' -:> K) (A1 ~[K' -:> K]~ A2) (prj[0] c)
| snd_app {K' : Kind}:
  SynthTerm G Δ Γ K ((A1 • B1) ~[K]~ (A2 • B2)) c ->
  SynthTerm G Δ Γ K' (A2 ~[K]~ B2) (prj[1] c)
| fst_arr {K : Kind}:
  SynthTerm G Δ Γ ★ ((A1 -:> B1) ~[★]~ (A2 -:> B2)) c ->
  SynthTerm G Δ Γ K (A1 ~[K]~ A2) (prj[0] c)
| snd_arr {K : Kind}:
  SynthTerm G Δ Γ ★ ((A1 -:> B1) ~[★]~ (A2 -:> B2)) c ->
  SynthTerm G Δ Γ K (A2 ~[K]~ B2) (prj[1] c)

| var  {i : Nat} :
  Γ[i]? = some (A ~[K]~ B) ->
  SynthTerm G Δ Γ K (A ~[K]~ B) #i
| global  {x : String}
  {As : Vec Ty na} {Bs : Vec Ty nb} {Ks : Vec Kind nc} {Cs : Vec Term nc}:
  lookup x G = some (.openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks1[i]) -> -- conjure universal tys
  (∀ i : Fin nb, G&Δ ⊢ Bs[i] : Ks2[i]) -> -- conjure existential tys
  (∀ i : Fin nc, SynthTerm G Δ (Bs.list ++ As.list ++ Γ) Ks[i] Ts[i] Cs[i]) ->
  SynthTerm G Δ Γ K R' (inst! x As Bs ts)
| inst {x : String}
  {As : Vec Ty na} {Bs : Vec Ty nb} {Ks : Vec Kind nc} {Cs : Vec Term nc} :
  lookup x G = some (.octor x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks1[i]) -> -- conjure universal tys
  (∀ i : Fin nb, G&Δ ⊢ Bs[i] : Ks2[i]) -> -- conjure existential tys
  (∀ i : Fin nc, SynthTerm G Δ (Bs.list ++ As.list ++ Γ) Ks[i] Ts[i] Cs[i]) ->
  SynthTerm G Δ Γ K R' (inst! x As Bs ts)

theorem synth_type_sound (wf : ⊢ G):
  SynthTerm G Δ Γ K T c ->
  G&Δ,Γ ⊢ c : T
| .refl j =>
  Typing.refl j
| @SynthTerm.sym _ _ _ _ A B c _ j e => by
  have lem := synth_type_sound wf j
  replace lem1 := terms_have_star_types wf lem
  cases lem1; case _ lem1a lem1b =>
  subst e
  apply Typing.cast (K := K)
  · apply Kinding.eq;
    apply Kinding.var; simp;
    apply Kinding.weaken;
    assumption
  · apply lem
  · simp; apply Typing.refl
    replace lem := terms_have_star_types wf lem
    cases lem; assumption
  · simp
| _ => sorry


def synth_term (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) (K : Kind) (wf : ⊢ G) : Ty -> Option Term
| (T1 ~[K]~ T2) => do
  let K'  <- T1.infer_kind G Δ
  let K'' <- T2.infer_kind G Δ
  if K' == K'' && K' == K
      then do
        let eG <- Ppcc.EqGraph.process_tyenv (G := G) (Δ := Δ) (Γ := Γ) (wf := wf)
        let ⟨t, _⟩ <- eG.ask (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) K T1 T2
        return t
      else none
| _ => none

theorem synth_sound (wf : ⊢ G):
  synth_term G Δ Γ K wf T = some c ->
  G&Δ, Γ ⊢ c : T
 := by
 intro j;
 unfold synth_term at j
 split at j
 · simp at j;
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨K', j1, j⟩
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨K'', j2, j⟩
   simp at j;
   rcases j with ⟨⟨e1, e2⟩, j⟩
   subst e1; subst e2
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨eG, j3, j⟩
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨⟨t, tj⟩, j4, j⟩
   simp at j; subst j; apply tj
 · cases j

end Core.Synth

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


def EqGraph.process_ty (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv)
 (eG : Ppcc.EqGraph G Δ Γ) (t : Term) (T : Ty) :
 Option (Ppcc.EqGraph G Δ Γ) := do
 match t0h : t.infer_type G Δ Γ with
 | some T' =>
   if he : T == T'
   then
     match h2 : T with
     | (T1 ~[K]~ T2) => do
        have lem0 := infer_type_sound wf t0h
        let ⟨i1, rep_T1, K1, _ , _⟩ <- eG.get_rep wf T1
        let ⟨i2, rep_T2, K2, _, _⟩ <- eG.get_rep wf T2
        if rep_T1 == rep_T2
        then return eG
        else if h : K1 == K2 && K2 == K
        then by {
          simp at h; rcases h with ⟨e1, e2⟩; subst K1; subst K2
          simp at he; subst he
          apply eG.process_equation G wf Δ Γ K T1 T2 ⟨t, lem0⟩ }
        else none
     | _ => return eG
   else none
 | none => none

def EqGraph.process_tyenv (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv) : Option (Ppcc.EqGraph G Δ Γ)
  := do let init : Ppcc.EqGraph G Δ Γ := Ppcc.EqGraph.empty
        let eG <- Γ.foldlM (λ acc T => acc.push_ty T) init
        (Γ.zip (List.range Γ.length)).foldlM (λ acc (t, i) => process_ty G wf Δ Γ acc #i t) eG

#guard List.range 3 == [0, 1, 2]

def TyEnv.is_consistent (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv) : Option Unit := do
  let eG <- EqGraph.process_tyenv G wf Δ Γ
  -- Get all global types

  -- get a pair of global type of the same kind

  -- Check if eG can build a coercion term for that type



def synth_coercion_term (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) : Ty -> Option Term
| (T1 ~[K]~ T2) => do
  let K'  <- T1.infer_kind G Δ
  let K'' <- T2.infer_kind G Δ
  if K' == K'' && K' == K
      then do
        match h : G.wf_globals with
        | some () =>
          let wf := wf_global_sound h
          let eG <- EqGraph.process_tyenv G wf Δ Γ
          let ⟨t, _⟩ <- eG.ask G wf Δ Γ K T1 T2
          return t
        | _ => none
      else none
| _ => none

theorem synth_coercion_sound :
  synth_coercion_term G Δ Γ T = some c ->
  G&Δ, Γ ⊢ c : T
 := by
 intro j;
 unfold synth_coercion_term at j
 split at j
 · simp at j;
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨K', j1, j⟩
   rw[Option.bind_eq_some_iff] at j; rcases j with ⟨K'', j2, j⟩
   simp at j;
   rcases j with ⟨⟨e1, e2⟩, j⟩
   subst e1; subst e2
   split at j
   · rw[Option.bind_eq_some_iff] at j; rcases j with ⟨eG, j3, j⟩
     rw[Option.bind_eq_some_iff] at j; rcases j with ⟨⟨t, tj⟩, j4, j⟩
     simp at j; subst j; apply tj
   · cases j
 · cases j


namespace Core.EqGraph.Test

def CtxWf : ⊢ [] := by constructor

def mEG1 : Option (Core.Ppcc.EqGraph [] [★, ★, ★, ★] [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])
  := EqGraph.process_tyenv (G := []) (Δ := [★, ★, ★, ★]) (wf := CtxWf) (Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2])

def test1 : Option Ty := do
  let eG <- mEG1
  let Δ := [★, ★, ★, ★]
  let Γ := [t#0 ~[★]~ t#1, t#1 ~[★]~ t#2]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ  ★ t#0 t#2
  Term.infer_type [] Δ Γ t
#eval! mEG1
#guard test1 == some (t#0 ~[★]~ t#2)

def mEG2 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)])
  := EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)]

#eval! repr mEG2

def test2 : Option Ty := do
  let eG <- mEG2
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★]
  let Γ := [(t#0 • t#2) ~[★]~ (t#1 • t#3)]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ (★ -:> ★) t#1 t#0
  Term.infer_type [] Δ Γ t

#guard test2 == some (t#1 ~[★ -:> ★]~ t#0)

def test3 : Option Ty := do
  let eG <- mEG2
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★]
  let Γ := [(t#0 • t#2) ~[★]~ (t#1 • t#3)]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#2) (t#3)
  Term.infer_type [] Δ Γ t

#guard test3 == some (t#2 ~[★]~ t#3)

def mEG3 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), t#4 ~[★]~ (t#1 • t#3)])
  := EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), t#4 ~[★]~ (t#1 • t#3)]

def test4 : Option Ty := do
  let eG <- mEG3
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★]
  let Γ := [t#4 ~[★]~ (t#0 • t#2), t#4 ~[★]~ (t#1 • t#3)]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#0 • t#2) (t#0 • t#3)
  Term.infer_type [] Δ Γ t

#eval! mEG3
#eval! mEG3.map (Ppcc.EqGraph.get_eq_class CtxWf · t#4)
#eval! ([t#4, t#0 • t#2].flatMap (λ a => List.map (Prod.mk a) [t#1 • t#3])).filter (λ (n1, n2) => n1 != t#4 || n2 != t#1 • t#3)
#guard test4 == some ((t#2) ~[★]~ (t#3))


end Core.EqGraph.Test


theorem env_consistency {G : GlobalEnv} {wf : ⊢ G} {Δ : KindEnv} {Γ : TyEnv} :
  TyEnv.is_consistent G wf Δ Γ = some () ->
  ∀ T1 T2 K, T1 ≠ T2 -> ¬ (G&Δ, Γ ⊢ c : (gt#T1 ~[K]~ gt#T2))
:= by
 intro h T1 T2 K ne j
 unfold TyEnv.is_consistent at h; simp at h

 sorry

end Core.Synth

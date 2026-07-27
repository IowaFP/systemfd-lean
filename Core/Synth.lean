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

def EqGraph.process_tyenv (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv) (i : Nat := Γ.length): Option (Ppcc.EqGraph G Δ Γ)
  := do let init : Ppcc.EqGraph G Δ Γ := Ppcc.EqGraph.empty
        let eG <- Γ.foldlM (λ acc T => acc.push_ty T) init
        (Γ.zip (List.range i)).foldlM (λ acc (t, i) => process_ty G wf Δ Γ acc #i t) eG


#guard List.range 3 == [0, 1, 2]


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
-- #eval! mEG1
#guard test1 == some (t#0 ~[★]~ t#2)

def mEG2 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)])
  := EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★] [(t#0 • t#2) ~[★]~ (t#1 • t#3)]

-- #eval! repr mEG2

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
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#2) (t#3)
  Term.infer_type [] Δ Γ t

-- #eval! mEG3
-- #eval! mEG3.map (Ppcc.EqGraph.get_eq_class CtxWf · t#4)
#guard test4 == some (t#2 ~[★]~ t#3)


def mEG4 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), (t#0 • t#2) ~[★]~ (t#1 • t#3)])
  := EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), (t#0 • t#2) ~[★]~ (t#1 • t#3)]

def test5 : Option Ty := do
  let eG <- mEG4
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★]
  let Γ := [t#4 ~[★]~ (t#0 • t#2), (t#0 • t#2) ~[★]~ (t#1 • t#3)]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#4) (t#1 • t#3)
  Term.infer_type [] Δ Γ t

-- #eval! mEG4
#guard test5 == some (t#4 ~[★]~ (t#1 • t#3))



def mEG5 : Option (Core.Ppcc.EqGraph [] [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#6, t#5 ~[★]~ t#6])
  := EqGraph.process_tyenv [] CtxWf [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★] [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#6, t#5 ~[★]~ t#6]


-- #eval! do
--   let eG <- mEG5
--   let T1 := t#4
--   let T2 := t#5
--   let K := ★
--   let G := []
--   let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★]
--   let Γ := [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#5]
--   let c := #2
--   let EGN := Ppcc.EqGraphNode G Δ Γ
--   let EG := Ppcc.EqGraph G Δ Γ

--   let j3 : G&Δ, Γ ⊢ c : (t#4 ~[★]~ t#5) := sorry
--   let ⟨ip1 ,rep_T1, Kp1, c1, jc1⟩ <- eG.get_rep CtxWf T1
--   let ⟨ip2 ,rep_T2, Kp2, c2, jc2⟩ <- eG.get_rep CtxWf T2
--   let clsT1 := eG.get_eq_class CtxWf T1
--   let clsT2 := eG.get_eq_class CtxWf T2
--   let p : List (EGN × EGN) := (clsT1.flatMap (λ a => List.map (Prod.mk a) clsT2)).filter (λ (n1, n2) => (n1.ty != T1 || n2.ty != T2))
--   let (p_app, p_not_app) : List (EGN × EGN) × List (EGN × EGN) := p.partition (λ (n1, n2) => n1.ty.is_app && n2.ty.is_app)
--   let eG' : EG <- p_app.foldlM (s := EG) (α := EGN × EGN) (m := Option) (init := eG) (λ acc (n1, n2) => do
--       let ⟨_, pT1, K1, η1, j1⟩ <- acc.get_rep CtxWf (Ppcc.EqGraphNode.ty n1)
--       let ⟨_, pT2, K2, η2, j2⟩ <- acc.get_rep CtxWf (Ppcc.EqGraphNode.ty n2)
--       if pT1 == pT2 then return acc
--       else if h : K1 == K2 && (K == K1 && (Kp1 == K && (Kp2 == K && (rep_T1 == pT1 && rep_T2 == pT2))))
--         then
--           by simp at h; rcases h with ⟨e1, e2, e3, e4, e5, e6⟩;
--              subst K1; subst K2; subst Kp1; subst Kp2; subst pT1; subst pT2
--              apply do
--                -- η1 ; symm c1; c; c2; symm η2
--                let ⟨symm_η2, symm_j2⟩ := Ppcc.EqGraph.symm [] CtxWf Δ Γ η2 K n2.ty rep_T2 j2
--                let ⟨symm_c1, symm_jc1⟩ := Ppcc.EqGraph.symm [] CtxWf Δ Γ c1 K T1 rep_T1 jc1
--                let ⟨c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ c2 symm_η2 K T2 rep_T2 n2.ty jc2 symm_j2
--                let ⟨c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ c c2_symm_η2 K T1 T2 n2.ty j3 j
--                let ⟨symm_c1_c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ symm_c1 c_c2_symm_η2 K rep_T1 T1 n2.ty symm_jc1 j
--                let ⟨η1_symm_c1_c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ η1 symm_c1_c_c2_symm_η2 K n1.ty rep_T1 n2.ty j1 j
--                acc.process_equation G CtxWf Δ Γ K n1.ty n2.ty ⟨η1_symm_c1_c_c2_symm_η2, j⟩
--         else none)

--   -- let eG' : EG <- p_not_app.foldlM (s := EG) (α := EGN × EGN) (m := Option) (init := eG') (λ acc (n1, n2) => do
--   --     let ⟨_, pT1, K1, η1, j1⟩ <- acc.get_rep CtxWf (Ppcc.EqGraphNode.ty n1)
--   --     let ⟨_, pT2, K2, η2, j2⟩ <- acc.get_rep CtxWf (Ppcc.EqGraphNode.ty n2)
--   --     if pT1 == pT2 then return acc
--   --     else if h : K1 == K2 && (K == K1 && (Kp1 == K && (Kp2 == K && (rep_T1 == pT1 && rep_T2 == pT2))))
--   --       then
--   --         by simp at h; rcases h with ⟨e1, e2, e3, e4, e5, e6⟩;
--   --            subst K1; subst K2; subst Kp1; subst Kp2; subst pT1; subst pT2
--   --            apply do
--   --              -- η1 ; symm c1; c; c2; symm η2
--   --              let ⟨symm_η2, symm_j2⟩ := Ppcc.EqGraph.symm [] CtxWf Δ Γ η2 K n2.ty rep_T2 j2
--   --              let ⟨symm_c1, symm_jc1⟩ := Ppcc.EqGraph.symm [] CtxWf Δ Γ c1 K T1 rep_T1 jc1
--   --              let ⟨c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ c2 symm_η2 K T2 rep_T2 n2.ty jc2 symm_j2
--   --              let ⟨c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ c c2_symm_η2 K T1 T2 n2.ty j3 j
--   --              let ⟨symm_c1_c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ symm_c1 c_c2_symm_η2 K rep_T1 T1 n2.ty symm_jc1 j
--   --              let ⟨η1_symm_c1_c_c2_symm_η2, j⟩ := Ppcc.EqGraph.seq G CtxWf Δ Γ η1 symm_c1_c_c2_symm_η2 K n1.ty rep_T1 n2.ty j1 j
--   --              acc.union CtxWf K n1.ty n2.ty η1_symm_c1_c_c2_symm_η2 j
--   --       else none)

--   return (p_app, p_not_app)

-- #eval! mEG5

def test6 : Option Ty := do
  let eG <- mEG5
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★]
  let Γ := [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#6, t#5 ~[★]~ t#6]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#1 • t#2) (t#1 • t#3)
  Term.infer_type [] Δ Γ t

#guard test6 == some ((t#1 • t#2) ~[★]~ ((t#1 • t#3)))

end Core.EqGraph.Test


end Core.Synth

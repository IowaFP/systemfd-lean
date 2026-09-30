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
  {As : Vec Ty na} {Bs : Vec Ty nb} {Ks : Vec Kind nc} {Cs : Vec Term nc} {R' R : Ty} :
  -- R' = R[(As.list ++ Bs.list).reverse ++ Subst.id Core.Ty] ->
  lookup x G = some (.octor x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) ->
  (∀ i : Fin na, G&Δ ⊢ As[i] : Ks1[i]) -> -- conjure universal tys
  (∀ i : Fin nb, G&Δ ⊢ Bs[i] : Ks2[i]) -> -- conjure existential tys
  (∀ i : Fin nc, SynthTerm G Δ Γ Ks[i] Ts[i] Cs[i]) ->
  SynthTerm G Δ Γ K R' (inst! x As Bs Cs.to)

theorem Vec.sum_le {e : Core.Term} {vs : Vec Core.Term n}:
  e ∈ vs ->
  e.size < (vs.map (·.size)).sum + 1
:= by
  intro h
  induction h
  simp; omega
  case _ ih => simp; omega

theorem Vec.fun_sum_le {e : Core.Term} {vs : Fun.Vec Core.Term n}:
  e ∈ vs.to ->
  e.size < (Fun.Vec.to (Core.Term.size <$> vs)).sum + 1
:= by
  intro h
  replace h := Vec.sum_le h
  have lem : (Vec.map (fun x => x.size) vs.to) = (Fun.Vec.to (Core.Term.size <$> vs)) := by
    apply Vec.ext_get; intro i
    simp [Vec.get_to]
  simp [<-lem]; apply h


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
| .inst (Cs := Cs) j1 j2 j3 j4 => by

  replace j1 := EntryWf.from_lookup wf j1
  cases j1; case _ j1 _ =>
  cases j1; case _ h1 h2 h3 h4 h5 =>
  apply Typing.spctor
  sorry
  sorry
  sorry
  apply j2
  apply j3
  · intro i; replace j4 := j4 i;
    have e : Cs.to i = Cs[i] := by apply Vec.to_get_elem
    rw [<-e] at j4; replace j4 := synth_type_sound wf j4; apply j4
  · simp; sorry
  · simp; sorry
  simp
  sorry
  sorry

| .global _ _ _ _ => sorry
| _ => sorry

termination_by
  c.size
decreasing_by
  subst e; simp
  simp; apply Vec.fun_sum_le; simp [<-Vec.get_to]; apply Vec.getElem_mem



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
          subst T; apply eG.process_equation G wf Δ Γ K T1 T2 ⟨t, lem0⟩ }
        else none
     | _ => return eG
   else none
 | none => none

def EqGraph.process_tyenv (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv) :
  Option (Ppcc.EqGraph G Δ Γ)
  := do let init : Ppcc.EqGraph G Δ Γ := Ppcc.EqGraph.empty
        let init <- G.foldlM (λ acc g => match g with
          | .data _ s _ _ => acc.push_ty gt#s
          | _ => acc) init
        let eG <- Γ.foldlM (λ acc T => acc.push_ty T) init
        (Γ.zipIdx).foldlM (λ acc (t, i) => process_ty G wf Δ Γ acc #i t) eG

def EqGraph.build_eq_graph (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) :
  Option (Ppcc.EqGraph G Δ Γ)
:= do
   match h : G.wf_globals with
   | some () =>
     let wf := wf_global_sound h
     let init : Ppcc.EqGraph G Δ Γ := Ppcc.EqGraph.empty
     let init <- G.foldlM (λ acc g => match g with
       | .data _ s _ _ => acc.push_ty gt#s
       | _ => acc) init
     let eG <- Γ.foldlM (λ acc T => acc.push_ty T) init
     (Γ.zipIdx).foldlM (λ acc (t, i) => process_ty G wf Δ Γ acc #i t) eG
   | none => none



def synth_coercion_term (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) : Ty -> Option Term
| (T1 ~[K]~ T2) => do
  let K'  <- T1.infer_kind G Δ
  let K'' <- T2.infer_kind G Δ
  if K' == K'' && K' == K
  then
    if T1 == T2 then return (refl! T1)
    else
    do
        match h : G.wf_globals with
        | some () =>
          let wf := wf_global_sound h
          let eG <- EqGraph.process_tyenv G wf Δ Γ
          let ⟨t, _⟩ <- eG.ask G wf Δ Γ K T1 T2
          return t
        | _ => none
  else none
| _ => none

theorem synth_coercion_term_sound :
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
   · case _ e =>
     simp at e; subst e; simp at j; subst c;
     have lem := infer_kind_sound j1; constructor; apply lem
   · split at j;
     · rw[Option.bind_eq_some_iff] at j; rcases j with ⟨eG, j3, j⟩
       rw[Option.bind_eq_some_iff] at j; rcases j with ⟨⟨t, tj⟩, j4, j⟩
       simp at j; subst j; apply tj
     · cases j
 · cases j


namespace Core.EqGraph.Test

theorem CtxWf : ⊢ [] := by constructor

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

-- #eval! mEG5

def test6 : Option Ty := do
  let eG <- mEG5
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★]
  let Γ := [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#6, t#5 ~[★]~ t#6]
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#1 • t#2) (t#1 • t#3)
  Term.infer_type [] Δ Γ t

#guard test6 == some ((t#1 • t#2) ~[★]~ ((t#1 • t#3)))

def test7 : Option Ty := do
  let eG <- mEG5
  let Δ := [★ -:> ★, ★ -:> ★, ★, ★, ★, ★, ★]
  let Γ := [t#4 ~[★]~ (t#0 • t#2), t#5 ~[★]~ (t#1 • t#3), t#4 ~[★]~ t#6, t#5 ~[★]~ t#6]
  -- let ⟨t1, _, _, _ ⟩ <- eG.get_rep_view CtxWf t#4
  -- let ⟨t2, _, _, _ ⟩ <- eG.get_rep_view CtxWf (t#1 • t#2)
  -- return (t1, t2)
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ Γ ★ (t#4) (t#1 • t#2)
  Term.infer_type [] Δ Γ t

#guard test7 == some ((t#4) ~[★]~ ((t#1 • t#2)))

def mEG6 :=  EqGraph.process_tyenv [] CtxWf [★, ★, ★] [t#0 ~[★]~ t#1, t#2 ~[★]~ t#2]

-- #eval! mEG6

def test8 := do
  let Δ := [★, ★, ★]
  let Γ := [t#0 ~[★]~ t#1, t#2 ~[★]~ t#2]
  let eG <- mEG6
  -- let ⟨t1, _⟩ <- eG.get_rep_view CtxWf (t#1 -:> t#2)
  -- let ⟨t2, _ ⟩ <- eG.get_rep_view CtxWf (t#0 -:> t#2)
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ  Γ ★ (t#0 -:> t#2) (t#1 -:> t#2)
  -- return (t1, t2, t)
  -- return eG
  Term.infer_type [] Δ Γ t

#guard test8 == some (t#0 -:> t#2 ~[★]~ (t#1 -:> t#2))

def mEG7 :=  EqGraph.process_tyenv [] CtxWf [★, ★, ★ -:> ★] [t#0 ~[★]~ (t#2 • t#1)]

def test9 := do
  let Δ := [★, ★, ★ -:> ★]
  let Γ := [t#0 ~[★]~ (t#2 •t#1)]
  let eG <- mEG7
  -- let ⟨t1, _⟩ <- eG.get_rep_view CtxWf (t#0 -:> t#2)
  -- let ⟨t2, _ ⟩ <- eG.get_rep_view CtxWf ((t#2 • t#1) -:> t#2)
  let ⟨t, _⟩ <- eG.ask [] CtxWf Δ  Γ ★ (t#0 -:> t#1) ((t#2 • t#1) -:> t#1)
  -- return (t1, t2 , t)
  -- return eG
  Term.infer_type [] Δ Γ t

-- #eval! test9
#guard test9 == some ((t#0 -:> t#1) ~[★]~ ((t#2 • t#1) -:> t#1))


-- def BoolCtx : GlobalEnv := [
--   Global.data 2 "Bool" ★
--              #( ("True", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩)
--                , ("False", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩)),
--   Global.data 2 "Ordering" ★
--              #( ("LT", ⟨0, #(), 0, #(), 0, #(), gt#"Ordering"⟩)
--                , ("GT", ⟨0, #(), 0, #(), 0, #(), gt#"Ordering"⟩))

--   ]

-- def WfBoolCtx : ⊢ BoolCtx := sorry

-- def mEG7 := EqGraph.process_tyenv BoolCtx WfBoolCtx [★] [t#0 ~[★]~ gt#"Bool"]

-- def test9 := do
--   let Δ := [★]
--   let Γ := [t#0 ~[★]~ gt#"Bool"]
--   let eG <- mEG7
--   let ⟨t, _⟩ <- eG.ask BoolCtx WfBoolCtx Δ Γ ★ (t#0 -:> gt#"Ordering") (gt#"Bool" -:> gt#"Ordering")
--   return t

-- #eval! mEG7
-- #eval! test9

end Core.EqGraph.Test

def List.unique_pairs {α : Type u} : List α -> List (α × α)
| [] => []
| .cons x xs => xs.map ( (x, ·) ) ++ unique_pairs xs

#eval List.unique_pairs [1,2,3]

-- Checks whether the eqns in Γ give rise to an inconsistent context
def isNotConsistent_aux (G : GlobalEnv) (wf : ⊢ G) (Δ : KindEnv) (Γ : TyEnv) (eG : Ppcc.EqGraph G Δ Γ)
: Option ((T1 : Ty) ×' (T2 : Ty) ×' (K : Kind) ×' (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) :=
  let gts := G.flatMap (λ g =>
    match g with
    | .data _ s _ _ => [gt#s]
    | _ => [])

  let ps := List.unique_pairs gts

  let ps' : List (Unit ⊕' ((T1 : Ty) ×' (T2 : Ty) ×' (K : Kind) ×' (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)))
    := ps.map (λ (x, y) => match x.infer_kind G Δ, y.infer_kind G Δ with
      | some K1, some K2 =>
        if h : K1 == K2 then
          by simp at h; subst h
             match eG.ask G wf Δ Γ K1 x y with
             | some ⟨t, j⟩ => apply (PSum.inr ⟨x, y, K1, t, j⟩)
             | none => apply PSum.inl ()
        else .inl ()
      | _, _ => .inl ())

  match ps'.findIdx? (λ x => match x with  | .inr _ => true  | .inl () => false ) with
  | some i =>
    match ps'[i]? with
    | some (.inr t) => t
    | _ => none
  | none => none


def isNotConsistent (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv)
  : Option ((T1 : Ty) ×' (T2 : Ty) ×' (K : Kind) ×' (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) := do
  match h : G.wf_globals with
  | some () =>
    let wf := wf_global_sound h
    let eG <- EqGraph.process_tyenv G wf Δ Γ
    isNotConsistent_aux G wf Δ Γ eG
  | none => none

-- TODO : what about cases like: Maybe a and Bool?


-- def Ty.ford (G : GlobalEnv) (Δ : KindEnv) (τ : Ty): Option SpineTy := do
--   let (x, tys) <- τ.spine
--   let na := tys.length
--   let univtys := (List.range (na)).reverse.map (t#·)
--   -- let tys := tys.map (λ (τ : Core.Ty) => τ[Subst.add (T := Core.Ty) (k := na)])

--   let univKs <- tys.mapM (Core.Ty.infer_kind G Δ ·)
--   let uv := Vec.from_list univKs

--   let tys := tys.map (λ (τ : Core.Ty) => τ[Subst.add (T := Core.Ty) (k := na)])

--   let eqs := ((univKs.zip univtys).zip tys).map (λ ((K, α),τ) =>  Core.Ty.eq K α τ)
--   let eqv := Vec.from_list eqs

--   return ⟨uv.1, uv.2, 0, #(), eqv.1, eqv.2, (gt#x).mkApps univtys⟩

-- theorem fording_sound :
--   G&Δ ⊢ τ : K ->
--   Ty.ford G Δ τ = some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩ ->
--   (Ks1.list ++ Ks2.list).reverse = Δ' ->
--   (∀ i : Fin nc, ∃ K : Core.Kind, G&(Δ'++ Δ) ⊢ Ts[i] : K) ∧ G&(Δ ++ Δ) ⊢ R : K
--    := by sorry



end Core.Synth

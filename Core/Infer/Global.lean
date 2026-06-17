import Core.Infer.Kind
import Core.Infer.Type

import Lilac
open Lilac

namespace Core

@[simp]
def GlobalEnv.wf_globals : GlobalEnv -> Option Unit
| .nil => return ()
| .cons (.data (n := n) x k ctors) G => do
  wf_globals G
  if (lookup x G).isNone && Vec.unique_elems (ctors.map (·.1)) then
    let mctors' : Vec (Option Unit) n := ctors.map (λ (c : String × SpineTy) =>
        spine_kinding (List.cons (.data 0 x k #()) G) (.data .cls) (c.1) (Ty.is_data x) c.2)
    let _ <- mctors'.sequence
    let mctors'' : Vec (Option Unit) n := ctors.map (λ c => if c.1 != x then some () else none)
    let _ <- mctors''.sequence
    let mctors'' : Vec (Option Unit) n := ctors.map (λ (c : String × SpineTy) =>
        if (lookup c.1 G).isNone then some () else none)
    let _ <- mctors''.sequence
  else none
| .cons (.openm x spTy) G => do
  wf_globals G
  if (lookup x G).isNone
  then spine_kinding G .openm x (λ _ => true) spTy
  else none
| .cons (.octor x spTy) G => do
  wf_globals G
  if (lookup x G).isNone
  then spine_kinding G (.data .opn) x (Ty.data? .opn G) spTy
  else none
| .cons (.defn x T t) G => do
  wf_globals G
  let T' <- t.infer_type G [] []
  let Tk <- T.infer_kind G []
  let _ <- Tk.base_kind
  if T == T' && (lookup x G).isNone then return () else none
| .cons (.inst x p t) G => do
  wf_globals G
  let e := lookup x G
  match e with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) => do
    if x == y
    then
      let Δ := (Ks1.list ++ Ks2.list).reverse
      let (ζ, Γ) <- pattern_binders G Δ n Ts p
      let R' <- t.infer_type G (ζ++Δ) Γ
      if R == R' then  return () else none
    else none
  | _ => none

| .cons (.odata x _) G => do
  wf_globals G
  if (lookup x G).isNone
  then return () else none

-- def OpenExhaustive (G : List Global) : Prop :=
--   ∀ {x na nb} {τ : Subst Ty} {As Ks : Vec _ na} {Ts Ts' : Vec _ nb} {Δ R q},
--   lookup x G = some (.openm x ⟨na, Ks, nb, Ts, R⟩) ->
--   (∀ (i : Fin na), G&Δ ⊢ As[i] : Ks[i]) ->
--   Sequ.append_vec (Vec.map su As) +0 = τ ->
--   Vec.map (·[τ]) Ts = Ts' ->
--   Query G .opn q Ts' ->
--   ∃ (i : Nat), ∃ b p, G[i]? = some (.inst x p b) ∧ Query.Match q p

def GlobalEnv.get_openm : GlobalEnv -> GlobalEnv :=
  List.filter (λ x =>
    match x with
    | .openm _ _ => true
    | _ => false)

def List.enumerate (l : List α) : List (Nat × α) :=
  let t := List.foldl (λ (i, acc) x => (i + 1, acc ++ [(i, x)])) (0, .nil) l
  t.snd


def GlobalEnv.check_insts (G : GlobalEnv) : Global -> Option Unit
| .openm x ⟨na, Ks, nb, Ts, R⟩ => do

  let G := List.enumerate G

  -- get all the instances of this method
  let ιs := G.filter (λ e => match e with
                             | (_, .inst y p _) => y == x
                             | _ => false )



  return ()
| _ => return ()


def GlobalEnv.check_open_exhaustive (G : GlobalEnv) : Option Unit := do
 let _ <- List.mapM (GlobalEnv.check_insts G) G

-- For each open method,
-- collect the instances of the method
-- collect the patterns for each instance
-- check that the patterns together are exhaustive

end Core

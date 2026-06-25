import Core.Infer.Kind
import Core.Infer.Type

open Lilac
open LeanSubst

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
| .cons (.inst (m := m) x p t) G => do
  wf_globals G
  match lookup x G with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) => do
    if x == y && m == n
    then
      let Δ := (Ks1.list ++ Ks2.list).reverse
      let (ζ, Γ) <- pattern_binders G Δ n Ts p
      let R' <- t.infer_type G (ζ++Δ) Γ
      if R⟨Ren.add Ty ζ.length⟩ == R' then return () else none
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


def GlobalEnv.check_insts (G : GlobalEnv) : Global -> Option (((ℓ1 : Nat) × ((m : Nat) × Vec (Pattern m) ℓ1)) × ((ℓ2 : Nat) × (n : Nat) × Vec (Fin n) ℓ2))
| .openm x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩ => do

  let octors <- (Ts.map (λ T : Ty => lookup_octor G T)).sequence
  let octors := octors.map (λ cs => Vec.from_list cs)
  let ref_matrix : (p : Nat) × Vec (Vec String (0 + nc)) p := Vec.populate octors

  -- get all the patterns from instances of this method
  let ιs : List (Pattern nc) := G.filterMap (λ e => match e with
         | (.inst (m := m) y p _) =>
           if h : y == x && m == nc
           then let p' : Pattern nc := p |> cast (by simp at h; rw[h.2])
                some p'
           else none
         | _ => none )
  let ιs := Vec.from_list ιs

  let mbs := ref_matrix.2.map (λ r => ((ιs.2.map (λ i => i.to_ctor_names |> cast (by rw[Nat.zero_add]))).findIdx! (· == r)))
  let mbs <- mbs.sequence

  return (⟨ιs.1, ⟨nc, ιs.2⟩⟩, ⟨ref_matrix.1, ⟨ιs.1, mbs⟩⟩)
| _ => return (⟨0, ⟨0, #()⟩⟩, ⟨0, ⟨0, #()⟩⟩)


def GlobalEnv.check_open_exhaustive (G : GlobalEnv) : Option Unit := do
 let _ <- List.mapM (GlobalEnv.check_insts G) G

-- For each open method,
-- collect the instances of the method
-- collect the patterns for each instance
-- check that the patterns together are exhaustive

end Core

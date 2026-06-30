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
      let (ζ, Γ) <- pattern_binders (.data .opn) G Δ n Ts p
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

def List.enumerate (l : List α) : List (Nat × α) :=
  let t := List.foldl (λ (i, acc) x => (i + 1, acc ++ [(i, x)])) (0, .nil) l
  t.snd

theorem List.enumerate_length {ls : List α} {ls' : List (Nat × α)}:
  List.enumerate ls = ls' ->
  ls'.length = ls.length := by sorry

theorem List.enumerate_indexing {ls : List α} {ls' : List (Nat × α)}:
  ∀ (h : i < ls.length),
  (h2 : List.enumerate ls = ls') ->
  ls'[i]'(by rw[List.enumerate_length (ls := ls) (ls' := ls')]; apply h; apply h2) = (i, ls[i])
:= by
  intro h1 h2
  unfold List.enumerate at h2
  simp at h2;

  sorry

def List.map_prov :
  List.map f ls = vs ->
  ∀ v ∈ vs, ∃ l ∈ ls, f l = v := by
intro h v v_in_vs
fun_induction List.map generalizing vs
subst h; simp at v_in_vs
case _ hd tl ih =>
  cases v_in_vs
  case _ => exists hd; simp; simp at h; apply h.1
  case _ b as v_in_vs =>
    simp at h;
    replace ih := ih h.2 v_in_vs
    rcases ih with ⟨l, ih1, ih2⟩
    exists l; apply And.intro;
    simp; apply Or.inr ih1
    apply ih2

def List.filter_prov :
  List.filter f ls = vs ->
  ∀ v ∈ vs, ∃ l ∈ ls, f l = true := by
intro h v v_in_vs
fun_induction List.filter f ls generalizing vs
subst h; simp at v_in_vs
case _ hd tl p ih =>
  cases v_in_vs
  · simp at h; rcases h with ⟨e, h⟩;
    subst e; subst h; exists hd; simp; apply p
  case _ v_in_vs =>
    simp at h; rcases h with ⟨e, h⟩;
    subst e; replace ih := ih h v_in_vs;
    rcases ih with ⟨l, ih1, ih2⟩
    exists l; simp
    apply And.intro (Or.inr ih1) ih2
case _ ih =>
  replace ih := ih h v_in_vs
  rcases ih with ⟨l, ih1, ih2⟩
  exists l; simp;
  apply And.intro (Or.inr ih1) ih2

def List.filter_then_map_prov :
  List.map f (List.filter p ls) = vs ->
  ∀ v ∈ vs, ∃ l ∈ ls, p l = true ∧ f l = v := by
intro h v v_in_vs

sorry
-- generalize zdef : List.filter p ls = zs at *
-- intro h v v_in_vs

-- have lem2 := List.map_prov h v v_in_vs
-- rcases lem2 with ⟨z, z_in_zs, zh⟩
-- have lem1 := List.filter_prov zdef z z_in_zs
-- rcases lem1 with ⟨l, l_in_ls, lh⟩
-- subst zdef;
-- have lem : z ∈ List.filter p ls -> z ∈ ls := by

--   sorry
-- exists l; exists l_in_ls; apply And.intro lh

-- sorry


def mk_open_pattern (x : String) (nc : Nat) :
  Global -> Option (Pattern nc)
| .inst (m := m) y p t =>
           if h : y == x && m == nc
           then some (p |> cast (by simp at h; rw[h.2]))
           else none
| _ => none

def mk_open_pattern_attach {G : GlobalEnv} (x : String) (nc : Nat) :
  {x : Global // x ∈ G} -> Option ({g : Global // g ∈ G})
| ⟨.inst (m := m) y p t, prop ⟩=>
           if h : y == x && m == nc
           then let p' : Pattern nc := (p |> cast (by simp at h; rw[h.2]))
                let prop' : Global.inst y p' t ∈ G := (prop |> cast (by simp at h; grind))
                return ⟨.inst (m := m) y p t, prop⟩
           else none
| _ => none



def mk_open_patterns (G : GlobalEnv) (x : String) (nc : Nat) :
    List (Pattern nc) :=
  match G with
  | .nil  => .nil
  | .cons g gs =>
    let ps := mk_open_patterns gs x nc
    match mk_open_pattern x nc g with
    | some p => p :: ps
    | none => ps

def mk_open_patterns_attach_aux (x : String) (nc : Nat) {G : GlobalEnv} : List {x : Global // x ∈ G} ->
    List ({g : Global // g ∈ G})
  | .nil => .nil
  | .cons g gs =>
    let ps := mk_open_patterns_attach_aux x nc gs
    match mk_open_pattern_attach x nc g with
    | some p => p :: ps
    | none => ps

def mk_open_patterns_attach (x : String) (nc : Nat) (G : GlobalEnv)
  := mk_open_patterns_attach_aux x nc (G := G) G.attach


def GlobalEnv.check_insts (G : GlobalEnv) : Global -> Option Unit
| .openm x ⟨_, _, _, _, nc, Ts, _⟩ => do

  -- get all the patterns from instances of this method
  let ps := mk_open_patterns G x nc
  let ⟨_, ps'⟩ := (Vec.from_list ps)

  -- check exhaustiveness of these patterns
  let _ <- check_exhaustive G Ts ps'

  return ()

| _ => return ()


def GlobalEnv.check_open_exhaustive (G : GlobalEnv) : Option Unit := do
  if G.all (λ g => (GlobalEnv.check_insts G g).isSome)
  then some ()
  else none

-- For each open method,
-- collect the instances of the method
-- collect the patterns for each instance
-- check that the patterns together are exhaustive

end Core

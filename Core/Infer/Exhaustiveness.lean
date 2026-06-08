
import Core.Ty
import Core.Global
import Core.Typing

import Core.Vec
import LeanSubst
import Lilac

open LeanSubst
open Lilac

namespace Core

def lookup_ctor_names (G : GlobalEnv) (T : Ty) : Option ((n : Nat) × Vec String n) := do
  let ⟨d, _⟩ <- T.spine
  match lookup d G with
  | some (.data _ _ ctors) =>
    return ⟨ctors.length, ctors.map (·.1) ⟩
  | _ => none

theorem lookup_ctor_names_sound :
  lookup_ctor? G DataConst.cls x T = true ->
  lookup_ctor_names G T = some ⟨n, cs⟩ ->
  ∃ j : Fin n, x = cs[j] := by
intro h1 h2

sorry


-- Given a vector of types, builds a matrix of all possible combination of constructor names
def enumerate_ctor_names {m : Nat} (G : GlobalEnv) (Ss : Vec Ty m) : Option ((n : Nat) × Vec (Vec String m) n) := do
  -- for each type in Ss get all the possible constructors
  let ctors <- (Vec.map (lookup_ctor_names G) Ss).seq
  return Vec.populate ctors


namespace Test

def Γ : GlobalEnv := [
  -- data Maybe a = Nothing | Just a
  Global.data 2 "Maybe" (★ -:> ★)
           #𝓋[ ("Nothing", ⟨1, #𝓋[★], 0, #𝓋[], (gt#"Maybe" • t#0)⟩) ,
               ("Just", ⟨1, #𝓋[★], 1,  #𝓋[t#0],  (gt#"Maybe" • t#0)⟩) ],
   Global.data 2 "Bool" ★
             #𝓋[ ("True", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)
               , ("False", ⟨0, #𝓋[], 0, #𝓋[], gt#"Bool"⟩)]
]


#eval (Vec.map (lookup_ctor_names Γ) (#𝓋[ (gt#"Maybe" • gt#"Bool"), gt#"Bool"])).seq
#eval enumerate_ctor_names Γ (#𝓋[ (gt#"Maybe" • gt#"Bool"), gt#"Bool", gt#"Bool"])
#eval Vec.append #𝓋[ "Nothing", "Just"] #𝓋[ "True" , "False" ]
#eval Vec.combine ⟨2, #𝓋[ #𝓋["Nothing", "()"], #𝓋["Just" , "()"]]⟩ ⟨3 , #𝓋[ "True" , "False" , "Med" ]⟩
#eval Vec.combine (k := 0) ⟨1, #𝓋[#𝓋[]]⟩ ⟨3 , #𝓋[ "True" , "False" , "Med" ]⟩

end Test

@[simp]
def Pattern.to_ctor_names (ps : Pattern m) : Vec String m :=  ps.map (λ p => p.1)

-- returns a matrix of constructor names from a pattern matrix
@[simp]
def patterns_to_ctor_names (ps : Vec (Pattern m) n) : Vec (Vec String m) n :=
 ps.map (λ x => x.to_ctor_names)

-- Checks that the patterns are exhaustive
def check_exhaustive (G : GlobalEnv) (Ss : Vec Ty m) (ps : Vec (Pattern m) n) : Option ((ℓ : Nat) × (Vec (Vec String m) ℓ × Vec (Fin n) ℓ)) := do
  let ref_matrix <- enumerate_ctor_names G Ss

  -- just keep the constructor names from the patterns
  let ps' := patterns_to_ctor_names ps

  -- check that each entry in ref_matrix has an associated entry ps'
  let mbs := ref_matrix.2.map (λ r => ps'.findIdx (λ x => x == r))
  let idxs <- mbs.seq
  return ⟨ref_matrix.fst, ⟨ref_matrix.snd , idxs⟩⟩

theorem pattern_match_rfl {q : Vec String m} {p : Pattern m} :
  p.to_ctor_names = q <-> Query.Match q p
:= by
apply Iff.intro
· intro h
  induction m <;> simp at *
  case _ =>
    unfold Query.Match;
    cases p; cases q; apply VecTyping.nil
  case _ ih =>
    unfold Query.Match
    cases q; case _ q qs =>
    cases p; case _ p ps =>
    simp at h
    apply VecTyping.cons
    · exists p.2.1; exists p.2.2.1; exists p.2.2.2
      rw[<-h.1]
    apply ih
    · apply h.2
· intro h
  induction h
  case _ => simp
  case _ h _ ih =>
    simp
    rcases h with ⟨_, _, _, h⟩
    cases h; simp; apply ih


theorem check_exhaustive_sound {G : GlobalEnv} {q : Vec String m} {S : Vec Ty m} :
  Query G DataConst.cls q S ->
  check_exhaustive G S ps = some ⟨ℓ, ⟨ref_matrix, idxs⟩⟩ ->
  ∃ j : Fin ℓ, ref_matrix[j] = q := by
intro h1 h2
unfold check_exhaustive at h2; simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨ref_matrix, h4, h2⟩
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨idxs, h6, h2⟩
replace h6 := Vec.map_seq_sound _ h6
cases h2;
cases ref_matrix; case _ n ref_matrix =>
simp at idxs;
simp at h6; simp
unfold enumerate_ctor_names at h4; simp at h4
rw[Option.bind_eq_some_iff] at h4; rcases h4 with ⟨ctor_names, h6, h4⟩
injection h4; case _ h4 =>
induction q;
case nil =>
  cases ctor_names
  cases ref_matrix
  case _ => simp at *
  case _ z _ => cases z; exists 0
case cons =>
  cases ctor_names
  replace h6 := Vec.map_seq_sound _ h6
  cases ref_matrix
  · simp; unfold Query at h1; cases h1;
    simp at h6; case _ h2 _ =>
    replace h6 := h6 0; simp at h6; rw[Fun.Vec.cons_zero, Fun.Vec.cons_zero] at h6
    have lem := lookup_ctor_names_sound h2 h6
    rcases lem with ⟨j, lem⟩; subst lem;
    simp at h4; simp at *; case _ ih =>
    sorry

  · sorry

end Core

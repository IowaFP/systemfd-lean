import LeanSubst
import Core.Ty
import Core.Global
import Core.Vec
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

-- returns a matrix of constructor names from a pattern matrix
@[simp]
def pattern_to_ctor_names (ps : Fun.Vec (Pattern m) n) : Fun.Vec (Vec String m) n := λ i =>
 Fun.Vec.to (λ j => ((ps i).get_elem j).1)


-- Checks that the patterns are exhaustive
def check_exhaustive (G : GlobalEnv) (Ss : Vec Ty m) (ps : Vec (Pattern m) n) : Option Unit := do
  let ⟨_, ref_matrix⟩ <- enumerate_ctor_names G Ss

  -- just keep the constructor names from the patterns
  let ps' := pattern_to_ctor_names ps.to

  -- check that each entry in ref_matrix has an associated entry ps'
  let mbs := ref_matrix.map (λ r => ps'.to.findIdx (λ x => x == r))
  let _ <- mbs.seq
  return ()

end Core

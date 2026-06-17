
import Core.Ty
import Core.Global
import Core.Typing

import Core.Vec
import LeanSubst
import Lilac

open LeanSubst
open Lilac

namespace Core

-- abbrev SpineTy := (m1 : Nat) × Vec Kind m1 × (m2 : Nat) × Vec Kind m2 × (n : Nat) × Vec Ty n × Ty

theorem ctor_data_linked {ctors : Vec _ n} {T : String} {spTy : SpineTy}{Tys : List Ty}:
  lookup T G = some (Entry.data T a ctors) ->
  lookup c G = some (Entry.ctor c k spTy) ->
  spTy.2.2.2.2.2.2.spine = some (T, Tys) ->
  ∃ i : Fin n, ctors[i].1 = c
:= by
intro h1 h2 h3

sorry


theorem lookup_ctor_names_sound :
  lookup_ctor? G DataConst.cls c T = true ->
  lookup_ctor_names G T = some ⟨n, cs⟩ ->
  ∃ j : Fin n, cs[j] = c := by
intro h1 h2
unfold lookup_ctor_names at h2; unfold lookup_ctor? at h1;
simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨spT, h4, h2⟩
split at h1
· rcases spT with ⟨Tx, Targs⟩; simp at h2; sorry
· cases h1


-- · cases h2; rw[h4] at h1; simp at h1; rw[Option.getD_eq_iff] at h1;
--   simp at h1
--   rcases h1 with ⟨e, h2, h3⟩
--   unfold Entry.ctor? at h3;
--   cases e <;> simp at h3
--   split at h3 <;> simp at *
--   subst h3;
--   case _ lk1 c k spTy _ _ e =>
--   have lem := lookup_name_eq lk1; cases lem
--   have lem := lookup_name_eq h2; cases lem; simp [Entry.name] at *
--   apply ctor_data_linked lk1 h2 e
-- · cases h2


-- Given a vector of types, builds a matrix of all possible combination of constructor names
def enumerate_ctor_names {m : Nat} (G : GlobalEnv) (Ss : Vec Ty m) : Option ((n : Nat) × Vec (Vec String m) n) := do
  -- for each type in Ss get all the possible constructors
  let ctors <- (Vec.map (lookup_ctor_names G) Ss).sequence
  let cs : (n : Nat) × Vec (Vec String m) n := Vec.populate ctors |> cast (by rw[Nat.zero_add])
  return cs


namespace Test

def Γ : GlobalEnv := [
  -- data Maybe a = Nothing | Just a
  Global.data 2 "Maybe" (★ -:> ★)
           #( ("Nothing", ⟨1, #(★), 0, #(), 0,  #(), (gt#"Maybe" • t#0)⟩) ,
               ("Just",    ⟨1, #(★), 0, #(), 1,  #(t#0),  (gt#"Maybe" • t#0)⟩) ),
   Global.data 2 "Bool" ★
              #(("True", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩),
                ("False", ⟨0, #(), 0, #(), 0, #(), gt#"Bool"⟩))
]


#eval (Vec.map (lookup_ctor_names Γ) (#( (gt#"Maybe" • gt#"Bool"), gt#"Bool"))).sequence
#eval enumerate_ctor_names Γ #( (gt#"Maybe" • gt#"Bool"), gt#"Bool", gt#"Bool")
#eval Vec.append #("Nothing", "Just") #("True" , "False")
#eval Vec.combine ⟨2, #( #("Nothing", "()"), #("Just" , "()"))⟩ ⟨3 , #( "True" , "False" , "Med" )⟩
#eval Vec.combine (k := 0) ⟨1, #(#())⟩ ⟨3 , #("True" , "False" , "Med")⟩

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
  let mbs := ref_matrix.2.map (λ r => ps'.findIdx? (λ x => x == r))
  let idxs <- mbs.sequence
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

-- theorem query_ctor_names {G : GlobalEnv} {q : Vec String m} {S : Vec Ty m} :
--   Query G DataConst.cls q S ->
--   (Vec.map (lookup_ctor_names G) S).seq = some ctor_names ->
--   ∃ idv: Vec ((n : Nat) × Fin n) m,
--   ∀ i : Fin m, q[i] = ctor_names[i].snd[j] := by
-- intro h1 h2 i
-- induction h1
-- apply i.elim0
-- case _ q qs ih1 =>
--   replace h2 := Vec.map_seq_sound _ h2 i
--   induction i using Fin.induction <;> simp at h2
--   · have lem := lookup_ctor_names_sound q h2
--     rcases lem with ⟨j, lem⟩
--     exists j
--   case _ i ih2 => cases ctor_names; case _ ctor_name ctor_names =>
--     apply ih1; simp at h2
--     clear ih2; revert i
--     sorry



theorem query_in_enumerate_ctors {G : GlobalEnv} {q : Vec String m} {S : Vec Ty m} :
  Query G DataConst.cls q S ->
  enumerate_ctor_names G S = some ⟨ℓ, ref_matrix⟩ ->
  ∃ j : Fin ℓ, ref_matrix[j] = q := by
intro h1 h2
unfold enumerate_ctor_names at h2; simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨ctor_names, h3, h2⟩
injection h2; case _ h2 =>
generalize z_def : Vec.populate_aux ⟨1, #(#())⟩ ctor_names = rm at *

-- have lem := query_ctor_names h1 h3

-- induction q
-- case nil =>
--   cases ctor_names
--   cases ref_matrix
--   simp at *
--   cases h1; subst h2;
--   simp at z_def; exists 0;
--   case _ v _ =>
--   cases v; simp
-- case cons ih =>
--   cases S; case _ S Ss =>
--   cases ctor_names; case _ ctor_name ctor_names =>

  -- cases ctor_names
  -- replace h7 := Vec.map_seq_sound _ h7
  -- simp at h7;
  -- cases h1;
  -- simp at z_def;
sorry

  -- cases ref_matrix
  -- · simp; unfold Query at h1; cases h1;
  --   simp at h6; case _ h2 _ =>
  --   replace h6 := h6 0; simp at h6; rw[Fun.Vec.cons_zero, Fun.Vec.cons_zero] at h6
  --   have lem := lookup_ctor_names_sound h2 h6
  --   rcases lem with ⟨j, lem⟩; subst lem;
  --   simp at h4; simp at *; case _ ih =>
  --   sorry


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
apply query_in_enumerate_ctors h1 h4

end Core

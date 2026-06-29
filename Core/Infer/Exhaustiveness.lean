import Core.Ty
import Core.Global
import Core.Typing

import Core.Vec

import Core.Metatheory.Global

open Lilac

namespace Core

-- abbrev SpineTy := (m1 : Nat) × Vec Kind m1 × (m2 : Nat) × Vec Kind m2 × (n : Nat) × Vec Ty n × Ty

theorem ctor_data_linked {ctors : Vec _ n} {T : String} {spTy : SpineTy}{Tys : List Ty}:
  ⊢ G ->
  lookup T G = some (Entry.data T a ctors) ->
  lookup c G = some (Entry.ctor c k spTy) ->
  spTy.2.2.2.2.2.2.spine = some (T, Tys) ->
  ∃ i : Fin n, ctors[i].1 = c
:= by
intro wf h1 h2 h3
replace h2 := EntryWf.from_lookup wf h2
cases h2; case _ i h2 h3 h4 h5 =>
cases h4; case _ h4 _ h6 =>
simp at h6; simp [Ty.is_data] at h4; rw[h6] at h4; simp at h4; subst T
rw[h2] at h1; simp at h1; rcases h1 with ⟨e1, e2, e3⟩;
subst e1; subst e2; replace e3 := eq_of_heq e3; subst e3;
exists i; rw[h3]

theorem octor_odata_linked {T : String} {spTy : SpineTy}{Tys1 Tys2 : List Ty}:
  ⊢ G ->
  lookup T G = some (Entry.odata T K) ->
  lookup c G = some (Entry.octor c spTy) ->
  spTy.2.2.2.2.2.2.spine = some (T, Tys1) ->
  lookup_octor G R = some ctors ->
  R.spine = some (T, Tys2) ->
  ∃ i : Nat, ctors[i]? = some c
:= by
intro wf h1 h2 h3 h4 h5
replace h2 := EntryWf.from_lookup wf h2
cases h2; case _ h2 h6 =>
unfold lookup_octor at h4;
simp at h4;
rw[Option.bind_eq_some_iff] at h4; rcases h4 with ⟨h4, h7, h8⟩
rw[h5] at h7; cases h7;
cases h2; simp at h3;

sorry
-- cases h2; case _ i h2 h3 h4 h5 =>
-- cases h4; case _ h4 _ h6 =>
-- simp at h6; simp [Ty.is_data] at h4; rw[h6] at h4; simp at h4; subst T
-- rw[h2] at h1; simp at h1; rcases h1 with ⟨e1, e2, e3⟩;
-- subst e1; subst e2; replace e3 := eq_of_heq e3; subst e3;
-- exists i; rw[h3]
theorem lookup_odata_entry_exists {G : GlobalEnv}:
  Ty.data? DataConst.opn G R = true ->
  R.spine = some (T, Tys) ->
  ∃ K, lookup T G = some (Entry.odata T K)
:= by
intro h1 h2
unfold Ty.data? at h1; rw[h2] at h1; simp at h1;
unfold is_data at h1;
generalize zdef : lookup T G = z at *
cases z; simp at h1
case _ e =>
simp at h1; cases e <;> simp [Entry.is_data] at *
have lem := lookup_name_agrees zdef; subst lem;
simp [Entry.name]

theorem lookup_data_entry_exists {G : GlobalEnv}:
  Ty.data? DataConst.cls G R = true ->
  R.spine = some (T, Tys) ->
  ∃ (K : Kind) (n : Nat) (ctors : Vec (String × SpineTy) n), lookup T G = some (Entry.data (n := n) T K ctors)
:= by
intro h1 h2
unfold Ty.data? at h1; rw[h2] at h1; simp at h1;
unfold is_data at h1;
generalize zdef : lookup T G = z at *
cases z; simp at h1
case _ e =>
simp at h1; cases e <;> simp [Entry.is_data] at *
have lem := lookup_name_agrees zdef; subst lem;
simp [Entry.name]



theorem lookup_octor_return_type_entry :
  ⊢ G ->
  lookup c G = some (Entry.octor c spTy) ->
  spTy.2.2.2.2.2.2.spine = some (T, Tys) ->
  ∃ K, lookup T G = some (Entry.odata T K)
:= by
intro wf h1 h2
replace h1 := EntryWf.from_lookup wf h1
cases h1; case _ h3 h1 =>
cases h3; case _ h4 _ =>
simp at h2;
apply lookup_odata_entry_exists h4 h2


theorem lookup_ctor_return_type_entry :
  ⊢ G ->
  lookup c G = some (Entry.ctor c n spTy) ->
  spTy.2.2.2.2.2.2.spine = some (T, Tys) ->
  ∃ (K : Kind) (n : Nat) (ctors : Vec (String × SpineTy) n), lookup T G = some (Entry.data (n := n) T K ctors)
:= by
intro wf h1 h2
replace h1 := EntryWf.from_lookup wf h1
cases h1; case _ h3 h1 =>
cases h3; case _ n _ K ctors _ lk _ _ _ _ _ _ _ _ _ _ _ h5 h4 _ =>
simp at h2;
unfold Ty.is_data at h5; rw[h2] at h5; simp at h5
subst h5; exists K; exists n; exists ctors


theorem lookup_entry_ctor? :
 ⊢ G ->
 lookup c G = some ent ->
 Entry.ctor? d dc ent = true ->
 ∃ c' K spTy tys, (ent = Entry.ctor c' K spTy ∨ ent = Entry.octor c' spTy) ∧ spTy.2.2.2.2.2.2.spine = some ⟨d, tys⟩
:= by
intro wf h1 h2
unfold Entry.ctor? at h2
have lem := lookup_name_agrees h1; simp [Entry.name] at lem; subst lem
split at h2 <;> simp at *
case _ c K _ _ _ _ _ _ _ =>
  exists c; exists K; simp;
  split at h2
  case _ sp _ => simp at h2; subst d; exists sp
  · cases h2
case _ c _ _ _ _ T sp _ =>
  exists c; simp;
  split at h2
  case _ sp _ => simp at h2; subst d; exists sp
  case _ => cases h2


theorem lookup_ctor_names_sound :
  ⊢ G ->
  lookup_ctor? G dc c T = true ->
  lookup_ctor_names G T = some ⟨n, cs⟩ ->
  ∃ j : Fin n, cs[j] = c := by
intro wf h1 h2
unfold lookup_ctor? at h1
unfold lookup_ctor_names at h2; simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨⟨Tx, Targs⟩, h4, h2⟩
split at h1
· simp at h2;
  rw[Option.getD_eq_iff] at h1; simp at h1
  rcases h1 with ⟨ent, h1, h3⟩
  split at h2
  case _ h0 _ _ _ _ _ h2 =>
    simp at h2; rcases h2 with ⟨e1, e2⟩;
    subst e1; replace e2 := eq_of_heq e2; simp at *
    have lem := lookup_name_agrees h1
    subst e2; simp
    replace h3 := lookup_entry_ctor? wf h1 h3; rcases h3 with ⟨c', K, spTy, tys, e, e2⟩
    cases e
    case _ e =>
      subst e; simp [Entry.name] at lem; subst c';
      have lem := lookup_name_agrees h2; simp [Entry.name] at lem; subst lem
      rw[h0] at h4; simp at h4; obtain ⟨e1, e2⟩ := h4
      subst e1; subst e2;
      have lem := ctor_data_linked wf h2 h1 e2
      apply lem
    case _ e =>
      subst e; simp [Entry.name] at lem; subst c';
      have lem := lookup_name_agrees h2; simp [Entry.name] at lem; subst lem
      rw[h0] at h4; simp at h4; obtain ⟨e1, e2⟩ := h4
      subst e1; subst e2;
      exfalso;
      have lem := lookup_octor_return_type_entry wf h1 e2
      rcases lem with ⟨K, lem⟩; rw[lem] at h2; simp at h2

  case _ h4 =>
    rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨cs, h2, h5⟩
    have lem := lookup_name_agrees h4; simp [Entry.name] at lem; subst lem;
    case _ tsp2 _ _ _  tsp1 =>
    rw[tsp1] at tsp2; simp at tsp2; rcases tsp2 with ⟨e1, e2⟩; subst e1; subst e2
    have lem := lookup_entry_ctor? wf h1 h3
    rcases lem with ⟨c1, K, spTy, Tys1, ch, Tys2⟩
    cases ch
    case _ ch =>
      subst ch;
      have lem := lookup_name_agrees h1; simp [Entry.name] at lem; subst lem;
      exfalso;
      unfold Entry.ctor? at h3;
      split at h3;
      · case _ e =>
          simp at e; rcases e with ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3; simp at *;
          rw[Tys2] at h3; simp at h3; clear h3;
          have lem := lookup_ctor_return_type_entry wf h1 Tys2
          rcases lem with ⟨K, n, ctors, lem⟩
          rw[lem] at h4; simp at h4
      · case _ e => simp at e
      · cases h3

    case _ ch =>
      subst ch
      have lem := lookup_name_agrees h1; simp [Entry.name] at lem; subst lem;
      have lem := octor_odata_linked wf h4 h1 Tys2 h2 tsp1
      simp at h5; rcases lem with ⟨i, lem⟩
      apply Vec.from_list_indexing h5 lem
  cases h2

· cases h1


-- Given a vector of types, builds a matrix of all possible combination of constructor names
def enumerate_ctor_names {m : Nat} (G : GlobalEnv) (Ss : Vec Ty m) : Option ((n : Nat) × Vec (Vec String m) n) := do
  -- for each type in Ss get all the possible constructors
  let ctors <- (Vec.map (lookup_ctor_names G) Ss).sequence
  let cs : (n : Nat) × Vec (Vec String m) n := Vec.populate ctors |> cast (by rw [Nat.zero_add])
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
#eval! enumerate_ctor_names Γ #( (gt#"Maybe" • gt#"Bool"), gt#"Bool", gt#"Bool")

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

theorem pattern_extension_enumerate {G : GlobalEnv} {S : Ty} :
  ⊢ G ->
  Vec.populate ctor_names = ⟨ℓ, ref_matrix⟩ ->

  lookup_ctor? G dc y S ->
  lookup_ctor_names G S = some ⟨nc, cs⟩ ->

  Vec.populate (⟨nc, cs⟩ :: ctor_names) = ⟨ℓ', ref_matrix'⟩ ->
  ∀ i : Fin ℓ, ∃ j' : Fin ℓ', ref_matrix'[j'] = y :: ref_matrix[i]
:= by
intro wf h3 h5 h6 h7 i
have lem := lookup_ctor_names_sound wf h5 h6
rcases lem with ⟨k, lem⟩;
unfold Vec.populate at h7; simp at h7; unfold Vec.populate at h3; rw[h3] at h7
have comb_size_lem := Vec.combine_size h7; simp at comb_size_lem
subst ℓ'
have lem1 := Vec.combine_soundness h7
simp at lem1;
replace lem1 := lem1 k i
rcases lem1 with ⟨j', lem1⟩
exists j'; rw[lem] at lem1;
apply Eq.symm lem1


theorem fin_shift_lemma {bs cs : Vec _ n} :
  (∀ (i : Fin (n + 1)), lookup_ctor_names G (b :: bs)[i] = some (c :: cs)[i]) ->
  ∀ (i : Fin n), lookup_ctor_names G bs[i] = some cs[i] := by
intro h i
replace h := h (i.succ); simp at h; apply h

theorem heq_cast_l {a : α} {b : β} {e : α = β} : a ≍ b -> a = (b |> cast (by rw[e]))
:= by subst e; simp;

theorem heq_cast_r {a : α} {b : β} {e : α = β}: a ≍ b -> cast (by rw[e]) a = b
:= by subst e; simp;

theorem cast_get_elem {a : Vec α ℓ} {b : Vec β ℓ} {e : α = β} (i : Fin ℓ):
  a ≍ b -> (cast (by rw[e]) a[i]) = b[i]
:= by intro h; subst e; replace h := eq_of_heq h; subst h; simp

theorem cast_cons {a : α} {b : Vec α n} {e : α = β} :
  cast (by rw[e]) (a :: b) = Vec.cons (cast (by rw[e]) a) (cast (by rw[e]) b)
:= by subst e; simp

-- set_option pp.explicit true

theorem cast_sigma (c0 : ((p : Nat) × Vec (Vec String (0 + (x + 1))) p) = ((n : Nat) × Vec (Vec String (x + 1)) n)) : cast c0 ⟨ℓ, z⟩ = ⟨ℓ', z'⟩ -> ℓ = ℓ' ∧ ∃ c, z = cast c z' := by
intro h; grind;

@[simp]
theorem Vec.cast_cons
  {e1 : n = m} {e2 : Vec α n = Vec α m}
  {x : α} {xs : Vec α n}
  : cast (by grind) (x :: xs) = x :: cast e2 xs
:= by
  cases e1; simp;

@[simp, grind =]
theorem Vec.cast_get {α β : Type u} {e1 : α = β}
  : ∀ {n : Nat} {e2 : Vec α n = Vec β n} {i : Fin n}, {v : Vec α n} -> cast e1 (v[i]) = (cast e2 v)[i]
| 0, e2, i, .nil => by simp [getElem]; grind
| n + 1, e2, i, .cons x xs => by
  cases i using Fin.cases
  case _ => cases e1; cases e2; simp
  case _ i => cases e1; cases e2; simp

theorem cast_indexing {z'h : Vec (Vec String (0 + x)) z'} {j' : Fin z'}
  {c1 : Vec String (0 + x) = Vec String x}
  {c2 : Vec (Vec String (0 + x)) z' = Vec (Vec String x) z'} :
  cast c1 (z'h[j']) = (cast c2 z'h)[j']
:= by grind

theorem query_in_enumerate_ctors {G : GlobalEnv} {q : Vec String m} {S : Vec Ty  m} :
  ⊢ G ->
  Query G dc q S ->
  enumerate_ctor_names G S = some ⟨ℓ, ref_matrix⟩ ->
  ∃ j : Fin ℓ, ref_matrix[j] = q := by
intro wf h1 h2
unfold enumerate_ctor_names at h2; simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨ctor_names, h3, h2⟩
injection h2; case _ h2 =>
replace h3 := Vec.map_seq_sound _ h3
unfold Query at h1;
induction h1 generalizing ℓ <;> simp at *
case _ =>
  generalize zdef : Vec.populate_aux ⟨1, #(#())⟩ ctor_names = z at *
  subst h2; cases ctor_names; simp at zdef;
  obtain ⟨e1, e2⟩ := zdef; subst e1; replace e2 := eq_of_heq e2; subst e2; simp;
case _ x _ _ lc _ ih =>
  generalize zdef : Vec.populate_aux ⟨1, #(#())⟩ ctor_names = z at *
  cases ctor_names; case _ c cs =>

  have z_size := Vec.populate_size _ zdef
  simp at z_size;
  have h3' := fin_shift_lemma h3
  replace h3 := h3 0; simp at h3
  have lem := lookup_ctor_names_sound wf lc h3
  obtain ⟨j, lem⟩ := lem
  simp at zdef;
  generalize zdef' : Vec.populate_aux ⟨1, #() :: #()⟩ cs = z' at *
  rcases z' with ⟨z', z'h⟩
  rcases z with ⟨z, zh⟩;

  have lem2 := Vec.combine_soundness zdef
  have lem0 : zh ≍ ref_matrix := by grind
  have lemz : z = ℓ := by grind
  subst z;

  -- c + z'h = zh ≍ ref_matrix

  replace lem2 := lem2 j

  subst lem; simp at lem2
  simp at z_size; subst ℓ

  replace ih := @ih z' (ref_matrix := z'h |> cast (by rw[Nat.zero_add])) _ (by {
    rw[zdef']; grind}) h3'
  rcases ih with ⟨j', ih⟩
  replace lem2 := lem2 j'
  rcases lem2 with ⟨j'', lem2⟩

  generalize c0_def : enumerate_ctor_names._proof_1 = c0 at *

  subst ih;
  exists j''

  have e1 : ref_matrix[j''] = cast (by simp) zh[j''] := by
    have h := cast_get_elem (e := by rw[Nat.zero_add]) j'' lem0
    rw[<-h]
  rw[e1]; rw[<-lem2]; clear lem2; norm_cast;
  generalize c2_def : of_eq_true
    (Eq.trans (congrFun' (congrArg Eq (congrArg (Vec String) (Nat.zero_add (x + 1)))) (Vec String (x + 1)))
      (eq_self (Vec String (x + 1))))  = c2 at *
  replace h2 := cast_sigma c0 h2;
  rcases h2 with ⟨_, c3, h3⟩

  have lem : ∃ c1, cast c2 (c.snd[j] :: z'h[j']) = Vec.cons (c.snd[j]) (cast c1 (z'h[j'])) := by
    grind
  rcases lem with ⟨c4, lem⟩
  rw[lem]; congr;
  apply cast_indexing


-- Checks that the patterns are exhaustive
def check_exhaustive (G : GlobalEnv) (Ss : Vec Ty m) (ps : Vec (Pattern m) n) : Option ((ℓ : Nat) × (Vec (Vec String m) ℓ × Vec (Fin n) ℓ)) := do
  let ref_matrix <- enumerate_ctor_names G Ss

  -- just keep the constructor names from the patterns
  let ps' := patterns_to_ctor_names ps

  -- check that each entry in ref_matrix has an associated entry ps'
  let mbs := ref_matrix.2.map (λ r => ps'.findIdx! (λ x => x == r))
  let idxs <- mbs.sequence
  return ⟨ref_matrix.fst, ⟨ref_matrix.snd , idxs⟩⟩


theorem check_exhaustive_sound {G : GlobalEnv} {q : Vec String m} {S : Vec Ty m} :
  ⊢ G ->
  Query G dc q S ->
  check_exhaustive G S ps = some ⟨ℓ, ⟨ref_matrix, idxs⟩⟩ ->
  ∃ j : Fin ℓ, ref_matrix[j] = q := by
intro wf h1 h2
unfold check_exhaustive at h2; simp at h2
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨ref_matrix, h4, h2⟩
rw[Option.bind_eq_some_iff] at h2; rcases h2 with ⟨idxs, h6, h2⟩
replace h6 := Vec.map_seq_sound _ h6
cases h2;
cases ref_matrix; case _ n ref_matrix =>
simp at idxs;
simp at h6; simp
apply query_in_enumerate_ctors wf h1 h4

end Core

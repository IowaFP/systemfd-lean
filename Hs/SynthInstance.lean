
import SystemFD
import Hs.EqGraph


-- Problem 2: producing a coercion
-- There is a term with a type `u : U` but the goal type is `V`
-- We need to try and find a coercion term `t : U ~ V` so that we can produce `u ▹ t : V`
-- The approach is two fold: refine the goal based off the structure of the coercion we need
--    and construct a graph of all possible coercions to search for a path from one type to another

-- For example, if we need `t : U1 -> U2 ~ V1 -> V2`, then we should immediately use the arrow coercion rule:
-- `?1 -c> ?2` with `?1 : U1 ~ V1` and `?2 : U2 ~ V2`
-- We also do this for the refl case

-- We use some semantic information to add instantiations of coercions (particularly for functional dependencies)
-- For example, if we know `u -> v` (u determines v) then we know that we ought to have three universally quantified
-- variables: `u`, `v1`, and `v2` with the equation `v1 ~ v2`
-- So, if we know that `F Int Bool` and `F Int b` then we "heuristically" produce the equation `Bool ~ b`
-- I say heuristically because you could imagine searching the context and producing all possible instantiations

-- For most situations when we are constructing instances it should be enough to just look at the available coercions
-- without having to do instantiations in the context.

-- The graph is constructed in the following way:
-- A coercion `t : U ~ V` becomes two edges `U -> V` with label `t` and `V -> U` with label `sym t`
-- A coercion `t : A B ~ C D` becomes two edges `A -> C` with label `t.1` and `B -> D` with label `t.2` (and of course the sym counterparts)
-- A coercion `t : ∀ K, A ~ B` searches for all instantiations of `K` and adds coercions recursively from there.

-- The instantiations are the worst issue here as it could theoretically explode.
-- A depth-first search is then run on the graph and the labels of the graph are returned.
-- These labels are joined by coercion sequencing: `t1 ; t2 ; ... ; tn` which produces the final coercion

-- TODO: Fix this, for now it assumes the argument list must be empty
def compute_argument_instantiation (Γ : Ctx Term) : Ctx Term -> List (SpineVariant × Term)
| args => []

-- TODO: add coercions built from ∀[K] A ~[★]~ ∀[K] B
def deconstruct_coercion_type (Γ : Ctx Term) (t : Term) : Term -> Term -> List (Term × Term × Term)
| A1 `@k B1, A2 `@k B2 =>
  let K := infer_kind Γ B1
  match K with
  | .some K =>
    let c1 := deconstruct_coercion_type Γ (fst! K t) A1 A2
    let c2 := deconstruct_coercion_type Γ (snd! K t) B1 B2
    c1 ++ c2
  | .none => []
| lhs, rhs => [(t, lhs, rhs)]

def construct_coercion_graph : Ctx Term -> EqGraph Term
| [] => EqGraph.empty_graph
| .cons (.type t) tl
| .cons (.openm t) tl =>
  let rest := construct_coercion_graph tl
  let (args, ret) := t.to_telescope
  let sp := compute_argument_instantiation tl args
  match ret.apply_spine sp with
  | lhs ~[_]~ rhs =>
    let v := Term.apply_spine #(List.length tl + 1) sp
    let edges := deconstruct_coercion_type tl v lhs rhs
    List.foldl (λ g (l, s, t) => g.add_edge l s t) rest edges
  | _ => rest
| .cons _ tl => construct_coercion_graph tl

def synth_coercion (Γ : Ctx Term) : Term -> Term -> Option Term
| A1 `@k B1, A2 `@k B2 => do
  let ac <- synth_coercion Γ A1 A2
  let bc <- synth_coercion Γ B1 B2
  return ac `@c bc
| A1 -t> B1, A2 -t> B2 => do
  let ac <- synth_coercion Γ A1 A2
  let bc <- synth_coercion (.empty::Γ) B1 B2
  return ac -c> bc
| ∀[K1] A1, ∀[K2] A2 => do
  let ac <- synth_coercion (.kind K1 :: Γ) A1 A2
  if K1 == K2 then .some (∀c[K1] ac)
  else .none
| lhs, rhs => do
  let K <- infer_kind Γ lhs
  let graph := construct_coercion_graph Γ
  let path <- graph.find_path_by_label (λ _ => false) lhs rhs
  return List.foldl (· `; ·) (refl! K lhs) path

-- Problem 1: filling in a hole
-- There is a goal that is an instance, say `C a b c`
-- We need to synthesize the evidence of this instance
-- Suppose the problem looks like this:

-- `class A; class B; class C; f : ∀ b c, B b c -> A b; g : ∀ a b c, A a -> C a b c; a; b; c; x : B a b ⊢ ? : C a b c`

-- First lets change the context to compute the telescopes:
-- `class A; class B; class C; f : (A b, [b, c, B b c]); g : (C a b c, [a, b, c, A a]); a; b; c; x : B a b ⊢ ? : C a b c`

-- Now we will exhaustively try every contextual telescope that matches the goal, in this case this is only one:
-- `Γ ⊢ g ?1 ?2 ?3 ?4` this produces four new goals, but it forces a = a, b = b, and c = c in the telescope

-- That means that `?1 = a`, `?2 = b`, and `?3 = c`, hence:
-- `Γ ⊢ g a b c ?4` with the goal: `Γ ⊢ ?4 : A a`

-- Now we recurse, exhaustively trying every contextual telescope that matches the goal, in this case this is only one:
-- `Γ ⊢ f ?5 ?6 ?7` this produces three new goals, but it forces b = a in the telescope

-- That means `?5 = a` giving us: `Γ ⊢ f a ?6 ?7`
-- Now we work on the _largest_ goal because it has the best chance of forcing other goals
-- We have: `Γ ⊢ ?7 : B a c` (note this c is indexed in the telescope, not the context)

-- Repeating the process again we get: `?7 = x` where `a = a` matches in the context, and it forces `c = b`
-- This gives us: `Γ ⊢ f a b x : A a` and finally `Γ ⊢ g a b c (f a b x) : C a b c`

  -- EqMaybe : ∀ t u. t ~ Maybe u → Eq u → Eq t
  -- Eq (Maybe Int) <- Goal
  -- t => Maybe Int -- Matching the goal type
  -- ∀ u. Maybe Int ~ Maybe u -> Eq u
  -- u  => Int -- Matching the coercion lhs & rhs
  -- Maybe Int ~ Maybe Int -> Eq Int
  -- refl @ refl -- by coercion synthesis
  -- Eq Int -- recurse

  -- match the goal type with the required type
  --     this ought to force all the "universally quantified variables"
  -- iterate over coercions, trying to find more forced stuff
  --     this ought to force all the "existentially quantified variables"
  --     might need to repeat this to compute a fixed point
  -- recurse on instance assumptions

def synth_instance (Γ : Ctx Term) (T : (Nat × List (SpineVariant × Term))) : Option Term := sorry

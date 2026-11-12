import Common.Vec

open LeanSubst
open Lilac

namespace Untyped

-- TODO: maybe turn into concrete record type
abbrev Pattern m := Vec (String × Nat × Nat) m

inductive Term : Type where
| var : Nat -> Term
| defn : String -> Term
| spctor : String -> Fun.Vec Term n -> Term
| app : Term -> Term -> Term
| lam : Term -> Term
| mtch m n : Fun.Vec Term m -> Fun.Vec (Pattern m) n -> Fun.Vec Term n -> Term


prefix:max "#" => Term.var
prefix:max "d#" => Term.defn

notation:70 f " • " a:70 => Term.app f a
notation "λ" t => Term.lam t

@[simp]
abbrev Term.unit := λ#0

@[coe]
def Term.from_action : Action Term -> Term
| .re y => #y
| .su t => t

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| #x => # (r.act x)
| d#x => d#x
| spctor x t => spctor x (rmap r <$> t)
| app f t => app (rmap r f) (rmap r t)
| lam t => lam (rmap r.lift t)
| mtch m n t1 t2 t3 => mtch m n (rmap r <$> t1) t2  (rmap r <$> t3)

instance : RenMap Term Term where
  rmap := Term.rmap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| #x => σ.act x
| d#x => d#x
| spctor x t => spctor x (smap σ <$> t)
| app t1 t2 => app (smap σ t1) (smap σ t2)
| lam t => lam (smap σ.lift t)
| mtch m n t1 t2 t3 => mtch m n (smap σ <$> t1) t2 (smap σ <$> t3)

instance : SubstMap Term Term where
  smap := Term.smap

/-- Untyped constructor. -/
def Constructor := String × (n : Nat) × Vec Term n

/-- Untyped Global -/
-- TODO: add data
inductive Global : Type where
| defn : String → Term → Global
| inst : String → Pattern m → Term → Global
/-- Included as a dummy variant to simplify indexing from source. -/
| erased

@[simp]
abbrev GlobalEnv := List Global

inductive Entry : Type where
| defn : String -> Term -> Entry

@[simp]
def lookup (x : String) : List Global → Option Entry
| [] => none
| .cons (.defn y t) tl => 
  if x == y then .some (.defn y t) else lookup x tl
| .cons _ tl => lookup x tl

@[simp]
def lookup_defn (G : List Global) (x : String) : Option Term := do
  let t <- lookup x G
  match t with
  | .defn _ t => return t

/-- Proposition that tracks when a vector
  of terms are part of a `spctor`.-/
inductive Term.IsData : Vec Term m -> Vec Constructor m -> Prop where
| nil : Term.IsData .nil .nil
| cons {t3 : Fun.Vec _ n} :
  Term.IsData ts cs ->
  Term.spctor c t3 = t ->
  ⟨c, n, t3.to⟩ = ct ->
  Term.IsData (t::ts) (ct::cs)

def Constructor.subst : Vec Constructor m -> List (Action Term)
| .nil => []
| .cons ⟨_, _, ts⟩ v => Constructor.subst v ++ ts.list.reverse.map su

inductive Pattern.Match : Vec Constructor m -> Pattern m -> Prop
| nil : Pattern.Match .nil .nil
| cons :
  Pattern.Match cs ps ->
  c = ⟨q, n, ts⟩ ->
  p = ⟨q, i, j⟩ ->
  Pattern.Match (c::cs) (p::ps)

inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
-- TODO: adjust. Maybe .unit • 
| beta : Red G ((λ b) • t) b[su t::+0σ]
| unit : Red G (t • .unit) t
----------------------------------------------------------------
---- Data Matching
----------------------------------------------------------------
| data_match {ss : Fun.Vec Term m} {ps : Fun.Vec (Pattern m) n} :
  Term.IsData ss.to ctors ->
  Pattern.Match ctors (ps i) ->
  b' = (bs i)[Constructor.subst ctors ++ Subst.id Term] ->
  Red G (.mtch m n ss ps bs) b'
| openm_match {i : Nat} {ss : Fun.Vec Term m} :
  Term.IsData ss.to ctors ->
  G[i]? = some (.inst x p b) ->
  Pattern.Match ctors p ->
  b' = b[Constructor.subst ctors ++ Subst.id Term] ->
  Red G (.spctor x ss) b'
----------------------------------------------------------------
---- Global Definitions
----------------------------------------------------------------
| defn :
  lookup_defn G x = some t ->
  Red G d#x t
----------------------------------------------------------------
---- Congruence Rules
----------------------------------------------------------------
| app_congr1 :
  Red G f f' ->
  Red G (f • a) (f' • a)
| app_congr2 :
  Red G a a' ->
  Red G (f • a) (f • a')
| match_congr {ss : Fun.Vec Term m} i :
  Red G (ss i) (ss' i) ->
  (∀ j ≠ i, ss j = ss' j) ->
  Red G (.mtch m n ss ps bs) (.mtch m n ss' ps bs)

notation:160 G:160 " ⊢ " t:160 " ~> " t':160 => Red G t t'

inductive RedOpt (G : GlobalEnv) : Term -> Term -> Prop where
| refl : RedOpt G x x
| step : Red G x y -> RedOpt G x z

notation:160 G:160 " ⊢ " t:160 " ~>? " t':160 => RedOpt G t t'

inductive RedStar (G : GlobalEnv) : Term -> Term -> Prop where
| refl : RedStar G x x
| step : RedStar G x y -> Red G y z -> RedStar G x z

notation:160 G:160 " ⊢ " t:160 " ~>* " t':160 => RedStar G t t'

inductive RedPlus (G : GlobalEnv) : Term -> Term -> Prop where
| one : Red G x y -> RedPlus G x y
| step : RedPlus G x y -> Red G y z -> RedPlus G x z

notation:160 G:160 " ⊢ " t:160 " ~>+ " t':160 => RedPlus G t t'

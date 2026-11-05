import Common.Vec

open LeanSubst
open Lilac

namespace Untyped

-- TODO: maybe turn into concrete record type
abbrev Pattern m := Vec (String × Nat × Nat) m

inductive Term : Type where
| unit : Term
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

@[coe]
def Term.from_action : Action Term -> Term
| .re y => #y
| .su t => t

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| unit => unit
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
| unit => unit
| #x => σ.act x
| d#x => d#x
| spctor x t => spctor x (smap σ <$> t)
| app t1 t2 => app (smap σ t1) (smap σ t2)
| lam t => lam (smap σ.lift t)
| mtch m n t1 t2 t3 => mtch m n (smap σ <$> t1) t2 (smap σ <$> t3)

instance : SubstMap Term Term where
  smap := Term.smap

inductive Global : Type where
| defn : String → Term → Global
| inst : String → Pattern m → Term → Global

@[simp]
abbrev GlobalEnv := List Global

-- We only need one lookup function for terms
def lookup (x : String) : List Global → Option Term
| [] => none
| .cons (.defn y t) tl => 
  if x == y then t else lookup x tl
-- Can express as a match expression
-- with only one case
| .cons (.inst y pm t) tl => 
  if x == y 
  then sorry
  -- then .some (.lam (.mtch m 1 #() #(pm) #(t)))
  else lookup x tl


inductive Red (G : List Global) : Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
-- TODO: adjust. Maybe .unit • 
| unit : Red G (t • .unit) t
| beta : Red G ((λ b) • t) b[su t::+0σ]
-- | prj_fst_app : Red G (prj[0] refl! (A • B)) (refl! A)
-- | prj_snd_app : Red G (prj[1] refl! (A • B)) (refl! B)
-- | prj_fst_arr: Red G (prj[0] refl! (A -:> B)) (refl! A)
-- | prj_snd_arr : Red G (prj[1] refl! (A -:> B)) (refl! B)
----------------------------------------------------------------
---- Global Definitions
----------------------------------------------------------------
| defn :
  lookup x G = some t ->
  Red G d#x t
----------------------------------------------------------------
---- Congruence Rules
----------------------------------------------------------------
| app_congr :
  Red G f f' ->
  Red G (f • a) (f' • a)
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

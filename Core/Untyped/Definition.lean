import Common.Vec

open LeanSubst
open Lilac

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


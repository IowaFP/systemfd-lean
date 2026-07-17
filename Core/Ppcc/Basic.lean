import Core.Ty
import Core.Term
import Core.Typing

import Core.Metatheory.Inversion
open LeanSubst

namespace Core.Ppcc

def getChild : Ty -> List Ty
| .var _ | .global _ | .all _ _ | .eq  _ _ _ => []
| .app A B => [A , B]
| .arrow A B => [A , B]

def subTerms : Ty -> List Ty
| .var i => [t#i]
| .global i => [gt#i]
| .all K A => [.all K A]
| .eq  K A B => [.eq K A B]
| .app A B => [A • B] ++ subTerms A ++ subTerms B
| .arrow A B => [A -:> B] ++ subTerms A ++ subTerms B


/-

Motivation:
Given a set of "named" equations:
e1 : a = b,
e2 : F a = F d
e3 : a = F d

We need to be able to do 2 things:
1. Check if the set of equations are consistent
  - Consistent meaning two different datatypes are never derived to be equal (we don't want Int ~ Bool)
2. When posed a question (an equation), such as, d = F d, be able to answer either:
   - The equation does not hold, or;
   - The equation does holds and give an explanation (a term) why they are equal

Standard techniques are insufficient because there is no notion of an explanation; (2) above.
as during the path compression in union-find DS, the explanations are essentially lost.

-/

structure Node (G : GlobalEnv) (Δ : KindEnv) where
  payload : (T : Ty) × (K : Kind) ×' (G&Δ ⊢ T : K)

@[simp, grind =]
def Node.get_ty (n : Node G Δ) : Ty := n.payload.1

structure EqGraphNode (G : GlobalEnv) (Δ : KindEnv) where
  parent : Nat
  rank : Nat
  payload : Node G Δ

@[simp, grind =]
def EqGraphNode.get_ty (n : EqGraphNode G Δ) : Ty := n.payload.get_ty

structure Edge (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) where
  payload : (t : Term) × (T : Ty) ×' G&Δ, Γ ⊢ t : T

@[simp, grind =]
def Edge.get_term (e : Edge G Δ Γ) : Term := e.payload.1

/-- Parent of a union-find node, defaults to self when the node is a root -/
def parentD (nodes : List (EqGraphNode G Δ)) (i : Nat) : Nat :=
  if h : i < nodes.length then nodes[i].parent else i

/-- Rank of a union-find node, defaults to 0 when the node is a root -/
def rankD (nodes : List (EqGraphNode G Δ)) (i : Nat) : Nat :=
  if h : i < nodes.length then nodes[i].rank else 0

structure EqGraph (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) where
  nodes : List (EqGraphNode G Δ)
  edges : List (Nat × Nat × Edge G Δ Γ)
  /-- Validity for parent nodes -/
  parentD_lt : ∀ {i}, (h : i < nodes.length) → nodes[i].parent < nodes.length
  /-- Validity for rank -/
  rankD_lt : ∀ {i}, parentD nodes i ≠ i → rankD node i < rankD nodes (parentD nodes i)


instance instMembershipTyEqGraph {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} : Membership Ty (EqGraph G Δ Γ) where
  mem eG T := List.elem T (eG.nodes.map (λ n => n.get_ty))

def EqGraph.elem_node {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (n : Node G Δ)(eG : EqGraph G Δ Γ) : Bool :=
  List.elem (n.get_ty) (eG.nodes.map (λ n => n.get_ty))

def EqGraph.push {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv}(eG : EqGraph G Δ Γ) (n : Node G Δ) : EqGraph G Δ Γ :=
  if eG.elem_node n
  then eG
  else { nodes := eG.nodes ++ [⟨eG.nodes.length, 0, n⟩]
       , edges := eG.edges
       , parentD_lt := by intro h1 h2; sorry
       , rankD_lt := sorry}

theorem EqGraph.push_makes_node {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {eG eG' : EqGraph G Δ Γ}
  {T : Ty} {K : Kind} {j : G&Δ ⊢ T : K} :
  (eG.push ⟨T, K, j⟩) = eG' ->
  T ∈ eG'
  := by
  unfold EqGraph.push;
  split <;> (intro h; rw[<-h])
  · assumption
  · unfold instMembershipTyEqGraph; simp

theorem EqGraph.push_keeps_edges {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {eG eG' : EqGraph G Δ Γ}
  {T : Ty} {K : Kind} {j : G&Δ ⊢ T : K} :
  (eG.push ⟨T, K, j⟩) = eG' ->
  eG.edges = eG'.edges
  := by
  unfold EqGraph.push;
  split <;> (intro h; rw[<-h])

-- Gets the representative node if the type exists
def EqGraph.get_rep {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) : Ty -> Option (Node G Δ)
  := sorry


def EqGraph.union {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) (K : Kind)
  (T1 : Ty) (T2 : Ty) (t : Term) (j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) : Option (EqGraph G Δ Γ) := do
  let i1 <- eG.nodes.findIdx? (·.get_ty == T1)
  let i2 <- eG.nodes.findIdx? (·.get_ty == T2)
  match eG.nodes[i1]?, eG.nodes[i2]? with
  | some n1, some n2 =>
    sorry
  | _, _ => none


theorem EqGraph.union_adds_edge {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {eG eG' : EqGraph G Δ Γ}  {K : Kind} {T1 T2 : Ty}
 (c : (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) (h1 : T1 ∈ eG) (h2 : T2 ∈ eG) :
 eG.union K T1 T2 c.1 c.2 = some eG' ->
 ∃ e ∈ eG'.edges, eG'.nodes[e.1]?.map (·.get_ty) = some T1 ∧ eG'.nodes[e.2.1]?.map (·.get_ty) = some T2 := by sorry

theorem EqGraph.union_keeps_nodes {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {eG eG' : EqGraph G Δ Γ}  {K : Kind} {T1 T2 : Ty}
 (c : (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) (h1 : T1 ∈ eG) (h2 : T2 ∈ eG) :
 eG.union K T1 T2 c.1 c.2 = eG' ->
 eG.nodes = eG'.nodes := by sorry


def EqGraph.find {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) : Ty -> Ty -> Option (Edge G Δ Γ) := sorry


def EqGraph.path {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) : Ty -> Ty -> Option (List (Edge G Δ Γ)) := sorry

def EqGraph.build_term {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} :
  List (Edge G Δ Γ) -> (t : Term) × (K : Kind) × (T1 : Ty) × (T2 : Ty) ×' (G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) := by sorry



def Term.sym (K : Kind) : Term := Λ[K]Λ[K] λ[t#1 ~[K]~ t#0] (.cast (t#0 ~[K]~ t#2) #0 (refl! t#1))
def Term.seq (K : Kind) : Term := Λ[K]Λ[K]Λ[K] λ[t#2 ~[K]~ t#1] λ[t#1 ~[K]~ t#0] .cast (t#3 ~[K]~ t#0) #0 #1


def EqGraph.symm {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G} (t : Term) (K : Kind) (T1 T2 : Ty) (j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) :
  (t : Term) ×' (G&Δ, Γ ⊢ t : (T2 ~[K]~ T1)) := ⟨(((Term.sym K) •[T1]) •[T2]) • t,
  by unfold Term.sym;
     apply Typing.app (A := T1 ~[K]~ T2)
     · have lem := terms_have_star_types wf j
       cases lem; case _ lem1 lem2 =>
       apply Typing.appt (K := K) (P := (T1⟨Ren.succ Ty⟩ ~[K]~ t#0) -:> (t#0 ~[K]~ T1⟨Ren.succ Ty⟩));
       · apply Typing.appt (K := K) (P := ∀[K] ((t#1 ~[K]~ t#0) -:> (t#0 ~[K]~ t#1)))
         · apply Typing.lamt;
           · apply Kinding.all; apply Kinding.all; apply Kinding.arrow;
             · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
             · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
           · apply Typing.lamt;
             · apply Kinding.all; apply Kinding.arrow;
               · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
               · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
             · apply Typing.lam
               · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
               · apply Typing.cast (K := K) (R' := t#0 ~[K]~ t#0⟨Ren.succ Ty⟩)
                 · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                 · apply Typing.var; simp; apply And.intro; rfl; rfl
                   apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                 · simp; apply Typing.refl; apply Kinding.var; simp
                 · simp
         · apply lem1
         · simp
       · apply lem2
       · simp
     · apply j⟩

theorem seq_subst_rename_lemma {TA TB : Ty} :
  TA⟨Ren.succ Ty⟩⟨Ren.succ Ty⟩[(su TB :: Subst.id Ty).lift] = TA⟨Ren.succ Ty⟩
  := by
    simp;
    rw[Subst.compose_ren_left]; simp;
    generalize σdef : (({ inner := fun n => re (n + 1) }) : LeanSubst.Subst Ty) = σ at *;
    generalize rdef : Ren.succ Ty = r at *
    have lem : r.to = σ := by
      rw[<-rdef]; rw[<-σdef]
      simp; unfold Subst.succ; simp
    have lem2 := Subst.apply_stable lem (S := Ty) (T := Ty)
    unfold SubstMap.smap; unfold instSubstMapTy;
    unfold RenMap.rmap; unfold instRenMapTy; simp;
    unfold SubstMap.smap at lem2; unfold instSubstMapTy at lem2;
    unfold RenMap.rmap at lem2; unfold instRenMapTy at lem2; simp at lem2;
    rw[lem2]

def EqGraph.seq {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G}
  (t1 t2: Term) (K : Kind) (TA TB TC : Ty) (j1 : G&Δ, Γ ⊢ t1 : (TA ~[K]~ TB)) (j2 : G&Δ, Γ ⊢ t2 : (TB ~[K]~ TC)) :
  (t : Term) ×' (G&Δ, Γ ⊢ t : (TA ~[K]~ TC)) := ⟨((((Term.seq K •[TA]) •[TB]) •[TC]) • t1) • t2, by
  unfold Term.seq
  have lem1 := terms_have_star_types wf j1
  cases lem1; case _ lemA lemB =>
  have lem2 := terms_have_star_types wf j2
  cases lem2; case _ lemC =>
  apply Typing.app (A := TB ~[K]~ TC)
  · apply Typing.app (A := TA ~[K]~ TB)
    · apply Typing.appt (K := K)
        (P := (TA⟨Ren.succ Ty⟩ ~[K]~ TB⟨Ren.succ Ty⟩) -:> (TB⟨Ren.succ Ty⟩ ~[K]~ t#0) -:> (TA⟨Ren.succ Ty⟩ ~[K]~ t#0))
      · apply Typing.appt (K := K)
           (P := ∀[K]((TA⟨Ren.succ Ty⟩⟨Ren.succ Ty⟩ ~[K]~ t#1) -:> (t#1 ~[K]~ t#0) -:> (TA⟨Ren.succ Ty⟩⟨Ren.succ Ty⟩ ~[K]~ t#0)))
        · apply Typing.appt (K := K) (P := ∀[K] ∀[K] (t#2 ~[K]~ t#1) -:> ((t#1 ~[K]~ t#0) -:> (t#2 ~[K]~ t#0)))
          · apply Typing.lamt
            · apply Kinding.all; apply Kinding.all; apply Kinding.all;
              apply Kinding.arrow;
              · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
              · apply Kinding.arrow;
                · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
            · apply Typing.lamt
              · apply Kinding.all; apply Kinding.all; apply Kinding.arrow;
                · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                · apply Kinding.arrow;
                  · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                  · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
              · apply Typing.lamt
                · apply Kinding.all; apply Kinding.arrow;
                  · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                  · apply Kinding.arrow;
                    · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                    · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                · apply Typing.lam
                  · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                  · apply Typing.lam
                    · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                    · apply Typing.cast (K := K) (A := t#1) (B := t#0)
                      apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                      apply Typing.var; simp;
                      · apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                      · apply Typing.var; simp; simp;
                        apply Kinding.eq; apply Kinding.var; simp; apply Kinding.var; simp
                      · simp
          · apply lemA
          · simp

        · apply lemB
        · rw[Ty.subst_all, Ty.subst_arr, Ty.subst_eq, Ty.subst_var, seq_subst_rename_lemma];
          rw[Ty.subst_arr, Ty.subst_eq, Ty.subst_eq]; rw[seq_subst_rename_lemma]; simp

      · apply lemC
      · simp

    · apply j1
  · apply j2⟩


def EqGraph.process_equation {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) (K : Kind) :
  (T1 : Ty) -> (G&Δ ⊢ T1 : K) -> (T2 : Ty) -> (G&Δ ⊢ T2 : K)  -> ((t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) -> Option (EqGraph G Δ Γ)
| T1, j1, T2, j2, ⟨c, j3⟩ =>
  let eG := eG.push ⟨T1, K, j1⟩
  let eG := eG.push ⟨T2, K, j2⟩
  eG.union K T1 T2 c j3

def EqGraph.empty {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} : EqGraph G Δ Γ := { nodes := [], edges := [], parentD_lt := nofun, rankD_lt := nofun}

def EqGraph.build_coercion {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (eG : EqGraph G Δ Γ) (T1 T2 : Ty) : Option (Edge G Δ Γ) :=  do
  let p1 <- eG.get_rep T1
  let p2 <- eG.get_rep T2
  if p1.get_ty == p2.get_ty
  then do
    let T1_to_p1 <- eG.path T1 p1.get_ty
    let T2_to_p2 <- eG.path T2 p2.get_ty



  none





end Core.Ppcc

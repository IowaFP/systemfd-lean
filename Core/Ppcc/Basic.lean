import Core.Ty
import Core.Term
import Core.Typing
import Core.Metatheory.Inversion

import Core.Infer
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
def Node.ty (n : Node G Δ) : Ty := n.payload.1
@[simp, grind =]
def Node.kind (n : Node G Δ) : Kind := n.payload.2.1


structure EqGraphNode (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) where
  parent : Nat × Ty × Kind

  -- rank : Nat
  payload : Node G Δ

  parent_rel : (t : Term) ×' (G&Δ, Γ ⊢ t : (payload.ty ~[payload.kind]~ parent.2.1))

@[simp, grind =]
def EqGraphNode.ty (n : EqGraphNode G Δ Γ) : Ty := n.payload.ty
@[simp, grind =]
def EqGraphNode.kind (n : EqGraphNode G Δ Γ) : Kind := n.payload.kind
@[simp, grind =]
def EqGraphNode.parent_ty (n : EqGraphNode G Δ Γ) : Ty := n.parent.2.1
@[simp, grind =]
def EqGraphNode.parent_kind (n : EqGraphNode G Δ Γ) : Kind := n.parent.2.2
@[simp, grind =]
def EqGraphNode.parent_idx (n : EqGraphNode G Δ Γ) : Nat := n.parent.1


structure EqGraph (G : GlobalEnv) (Δ : KindEnv) (Γ : TyEnv) where
  nodes : List (EqGraphNode G Δ Γ)

  /-- Validity for parent nodes -/
  -- parent index is less than the length of the nodes
  parent_lt : ∀ {i}, (h : i < nodes.length) -> nodes[i].parent_idx < nodes.length

  parent_idx_lt : ∀{i}, (h : i < nodes.length) -> nodes[i].parent_idx ≤ i

  /-- parent kind is equal to the node kind -/
  parent_kind_eq : ∀{i}, (h : i < nodes.length) -> nodes[i].parent_kind = nodes[i].kind

  /- parent type matches the type stored in the nodes parent -/
  parent_ty_eq : ∀{i}, (h : i < nodes.length) -> nodes[i].parent_ty = (nodes[nodes[i].parent_idx]'(parent_lt _)).ty

instance instMembershipTyEqGraph {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} : Membership Ty (EqGraph G Δ Γ) where
  mem eG T := List.elem T (eG.nodes.map (·.ty))

def EqGraph.elem_node {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (n : Node G Δ)(eG : EqGraph G Δ Γ) : Bool :=
  List.elem (n.ty) (eG.nodes.map (λ n => n.ty))

def EqGraph.empty {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} : EqGraph G Δ Γ
  := { nodes := [], parent_lt := nofun, parent_idx_lt:= nofun, parent_kind_eq := nofun, parent_ty_eq := nofun  }

def EqGraph.push {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv}(eG : EqGraph G Δ Γ) (n : Node G Δ) : EqGraph G Δ Γ :=
  if eG.elem_node n
  then eG
  else let new_node := {
         parent := (eG.nodes.length, n.ty, n.kind),
         payload := n,
         parent_rel := ⟨refl! n.ty, by apply Typing.refl; apply n.payload.2.2⟩
         }
       { nodes := eG.nodes ++ [new_node]
       , parent_lt := by
          intro i h1;
          simp;
          simp only [List.length_append] at h1; simp at h1;
          rw[List.getElem_append]
          split
          case _ h => have lem := eG.parent_lt (i := i) h; simp [EqGraphNode.parent_idx] at lem; omega
          case _ h =>
            have lem : i = eG.nodes.length := by omega
            subst lem; simp [new_node]

       , parent_idx_lt := by
           intro i h1
           simp;
           simp only [List.length_append] at h1; simp at h1
           rw[List.getElem_append]
           split
           case _ h => apply  eG.parent_idx_lt h
           case _ h =>
             have lem : i = eG.nodes.length := by omega
             subst lem; simp [new_node]
       , parent_kind_eq := by
            intro i h1;
            rw[List.getElem_append]
            split
            case _ h => apply eG.parent_kind_eq h
            case _ h =>
              have lem : i = eG.nodes.length := by rw[List.length_append] at h1; simp at h1; omega
              subst i; simp[new_node]; congr; simp; simp
       , parent_ty_eq := by
           intro i h1;
           cases Nat.decLt i eG.nodes.length
           case _ h =>
             have lem : i = eG.nodes.length := by rw[List.length_append] at h1; simp at h1; omega
             subst i; simp [new_node]
           case _ h =>
             have lem := eG.parent_lt h
             have lem2 : (eG.nodes ++ [new_node])[i] = eG.nodes[i] := by rw[List.getElem_append_left]
             have lem3 := eG.parent_ty_eq h
             simp [EqGraphNode.parent_idx] at lem
             conv =>
               lhs
               rw [lem2, lem3]
             simp [lem2];
             conv =>
               rhs
               rw[List.getElem_append_left lem]
        }

theorem EqGraph.push_makes_node {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {eG eG' : EqGraph G Δ Γ}
  {T : Ty} {K : Kind} {j : G&Δ ⊢ T : K} :
  (eG.push ⟨T, K, j⟩) = eG' ->
  T ∈ eG'
  := by
  unfold EqGraph.push;
  split <;> (intro h; rw[<-h])
  · assumption
  · unfold instMembershipTyEqGraph; simp

def EqGraph.get_rep_aux {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (wf : ⊢ G) (eG : EqGraph G Δ Γ)
  (T1 : Ty) (i : Nat) (h : i < eG.nodes.length) :
  Option ((Nat) × (T2 : Ty) × (K : Kind) × (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) := do
    let n := eG.nodes[i]
    have lem1 := eG.parent_kind_eq h
    have lem2 := eG.parent_ty_eq h
    have lem3 := eG.parent_idx_lt h
    have lem4 := n.parent_rel.2
    if h2 : n.parent_idx == i && n.ty == T1
    then
      by simp at h2;
         rcases h2 with ⟨h2a, h2b⟩
         apply some ⟨i, n.parent.2.1, n.kind, n.parent_rel.1,
               by rw[<-lem1]; rw[<-h2b]; rw[lem1]; simp [n, Node.ty] at lem4; simp [n, Node.ty]; apply lem4⟩
    else
      if h2' : n.parent_idx < i && n.ty == T1
      then { by
      simp at h2'; rcases h2' with ⟨e1, e2⟩
      let ih := EqGraph.get_rep_aux wf eG n.parent_ty n.parent_idx
                        (by unfold EqGraphNode.parent_idx; omega)
      match ih with
      | some ⟨i, T3, k, η, ih⟩ =>
        if h3 : n.kind == k
          then
            simp at h3; simp [Node.kind] at lem4; simp only [e2, h3] at lem4;
            have lem5 := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) n.parent_rel.1 η k T1 n.parent_ty T3 lem4 ih
            rcases lem5 with ⟨η', j⟩
            apply some ⟨i, T3, k, η', j⟩
          else apply none
      | none => apply none }
      else none

-- Gets the representative node if the type exists
def EqGraph.get_rep {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (wf : ⊢ G) (eG : EqGraph G Δ Γ) (T1 : Ty) : Option (Nat × (T2 : Ty) × (K : Kind) × (t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) := do
  let i <- eG.nodes.findIdx? (·.ty == T1)
  if h1 : (i < eG.nodes.length)
  then EqGraph.get_rep_aux wf eG T1 i h1
  else none


def EqGraph.union {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G} (eG : EqGraph G Δ Γ) (K : Kind)
  (T1 : Ty) (T2 : Ty) (t : Term) (j : G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) : Option (EqGraph G Δ Γ) := do
  let i1 <- eG.nodes.findIdx? (·.ty == T1)
  let i2 <- eG.nodes.findIdx? (·.ty == T2)
  match eG.nodes[i1]?, eG.nodes[i2]? with
  | some n1, some n2 => do
    let ⟨ip1, pT1, K1, η1, j1⟩ <- eG.get_rep wf T1
    let ⟨ip2, pT2, K2, η2, j2⟩ <- eG.get_rep wf T2
    let p1n <- eG.nodes[ip1]?
    let p2n <- eG.nodes[ip2]?
    if ip1 == ip2
    then return eG -- both T1 and T2 are already in the same eq class
    else
      if h : ip1 < ip2 && ip2 < eG.nodes.length && K1 == K2 && n2.kind == K1 && n1.kind == K1 && K == K1 && p1n.ty == pT1 && p1n.kind == K1 && p2n.ty == pT2 && p2n.kind == K2
      then
        -- pT2 == T2 == T1 == pT1
        -- symm η2 ; (symm t ; η1)
        let new_node : EqGraphNode G Δ Γ := {
          parent := (ip1, pT1, K1)
          payload := p2n.payload
          parent_rel :=
            let ⟨symm_t, j'⟩ := EqGraph.symm (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) t K T1 T2 j
            let ⟨symm_η2, j2'⟩ := EqGraph.symm (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) η2 K2 T2 pT2 j2
            let ⟨symm_t_η1, j⟩ := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) symm_t η1 K T2 T1 pT1 j'
                         (by simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; apply j1)
            let ⟨symm_η2_symm_t_η1, j⟩ := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) symm_η2 symm_t_η1 K2 pT2 T2 pT1 j2'
                         (by simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2; apply j)
            ⟨symm_η2_symm_t_η1, by
              simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
              simp only [Node.ty, e8, Node.kind, e9]; apply j⟩ }
        some { nodes := eG.nodes.set ip2 new_node
             , parent_lt := by
                 intro i h1;
                 simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
                 simp; -- generalize ndef : (eG.nodes.set ip2 new_node)[i] = n at *;
                 have lem := List.getElem_mem h1
                 have lem2 := List.mem_or_eq_of_mem_set lem
                 cases lem2
                 case inl h =>
                   rw[List.mem_iff_getElem] at h;
                   rcases h with ⟨n, h', e11⟩
                   rw[<-e11]; apply eG.parent_lt
                 case inr h => simp only [h, new_node]; omega
             , parent_idx_lt := by
                  intro i h1;
                  simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
                  simp;
                  have lem := List.getElem_mem h1
                  have lem2 := List.mem_or_eq_of_mem_set lem
                  cases lem2
                  case inl h =>
                   rw[List.mem_iff_getElem] at h;
                   rcases h with ⟨n, h', e11⟩
                   rw[<-e11]; sorry

                  case inr h => simp only [h, new_node]; sorry
             , parent_kind_eq := by
                  intro i h1
                  simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
                  simp;
                  have lem := List.getElem_mem h1
                  have lem2 := List.mem_or_eq_of_mem_set lem
                  cases lem2
                  case inl h =>
                   rw[List.mem_iff_getElem] at h;
                   rcases h with ⟨n, h', e11⟩
                   rw[<-e11]; apply eG.parent_kind_eq

                  case inr h' => rw[h']; simp only [new_node]; symm; apply e9

             , parent_ty_eq := by
                  intro i h1
                  simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
                  simp;
                  have lem := List.getElem_mem h1
                  have lem2 := List.mem_or_eq_of_mem_set lem
                  cases lem2
                  case inl h =>
                   rw[List.mem_iff_getElem] at h;
                   rcases h with ⟨n, h', e11⟩
                   simp only [<-e11]; sorry

                  case inr h' => simp only [h', new_node]; sorry

             }
      else if h : ip2 < ip1 && ip1 < eG.nodes.length && K1 == K2 && n2.kind == K1 && n1.kind == K1 && K == K1 && p1n.ty == pT1 && p1n.kind == K1 && p2n.ty == pT2 && p2n.kind == K2
        then
        -- pT1 == T1 == T2 == pT2
        -- sym η1 ; t ; η2
         let new_node : EqGraphNode G Δ Γ := {
           parent := (ip2, pT2, K2)
           payload := p1n.payload
           parent_rel :=
            let ⟨symm_η1, j'⟩ := EqGraph.symm (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) η1 K1 T1 pT1 j1

            let ⟨t_η2, j⟩ := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) t η2 K T1 T2 pT2 j
                         (by simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2; apply j2)
            let ⟨symm_η1_t_η2, j⟩ := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) symm_η1 t_η2 K pT1 T1 pT2
                         (by simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2; apply j')
                         (by simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2; apply j)
            ⟨symm_η1_t_η2, by
              simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
              simp only [Node.ty, Node.kind, e6, e7]; apply j⟩ }
         some { nodes := eG.nodes.set ip2 new_node
              , parent_lt := by
                  intro i h1;
                  simp at h; rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩; subst e5; subst e2
                  simp;
                  have lem := List.getElem_mem h1
                  have lem2 := List.mem_or_eq_of_mem_set lem
                  cases lem2
                  case inl h =>
                    rw[List.mem_iff_getElem] at h;
                    rcases h with ⟨n, h', e11⟩
                    rw[<-e11]; apply eG.parent_lt
                  case inr h => simp only [h, new_node]; omega
              , parent_idx_lt := sorry
              , parent_kind_eq := sorry
              , parent_ty_eq := sorry  }
        else none
  | _, _ => none


-- theorem Typing.app_split {G : GlobalEnv} {Δ : KindEnv} :
--   G&Δ  ⊢ (A • B) : K ->
--   ∃ K', G&Δ ⊢ A : (K' -:> K) ∧ G&Δ ⊢ B : K'
-- | .app (A := K') j1 j2 => by exists K'

-- theorem Typing.app_first_kind_eq {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (wf : ⊢ G):
--   G&Δ , Γ ⊢ c : ((A1 • B1) ~[K]~ (A2 • B2)) ->
--   ∃ K', G&Δ ⊢ A1 : (K' -:> K) ∧ G&Δ ⊢ B1 : (K' -:> K) := by
--   intro j
--   have lem := terms_have_star_types wf j

--   sorry


-- theorem Typing.app_first {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} (wf : ⊢ G):
--   G&Δ , Γ ⊢ c : ((A1 • B1) ~[K]~ (A2 • B2)) ->
--   ∃ K', G&Δ,Γ ⊢ (prj[0] c) : (A1 ~[K' -:> K]~ A2) ∧ G&Δ , Γ ⊢ (prj[1] c) : (B1 ~[K']~ B2) := by
--   intro j
--   have lem := terms_have_star_types wf j
--   cases lem; case _ lem1 lem2 =>
--   cases lem1; cases lem2;

--   sorry



def EqGraph.process_equation {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G} (eG : EqGraph G Δ Γ) (K : Kind) :
  (T1 : Ty) -> (G&Δ ⊢ T1 : K) -> (T2 : Ty) -> (G&Δ ⊢ T2 : K)  -> ((t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2)) -> Option (EqGraph G Δ Γ)
-- | (.app A1 B1), j1, (.app A2 B2), j2, ⟨c, j3⟩ =>
--   let T1 := A1 • B1
--   let T2 := A2 • B2
--   let eG := eG.push ⟨T1, K, j1⟩
--   let eG := eG.push ⟨T2, K, j2⟩
--   eG.union (wf := wf) K T1 T2 c j3
  -- cannot do this
  -- ⟨K, lem1, lem2⟩ := Typing.app_first_kind_eq j1

| T1, j1, T2, j2, ⟨c, j3⟩ =>
  let eG := eG.push ⟨T1, K, j1⟩
  let eG := eG.push ⟨T2, K, j2⟩
  eG.union (wf := wf) K T1 T2 c j3

def EqGraph.ask {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G} (eG : EqGraph G Δ Γ) (K : Kind)
  (T1 : Ty) (T2 : Ty) : Option ((t : Term) ×' G&Δ, Γ ⊢ t : (T1 ~[K]~ T2))
:= do
  let i1 <- eG.nodes.findIdx? (·.ty == T1)
  let i2 <- eG.nodes.findIdx? (·.ty == T2)
  match eG.nodes[i1]?, eG.nodes[i2]? with
  | some n1, some n2 => do
    let ⟨ip1, pT1, K1, η1, η1_j⟩ <- eG.get_rep wf T1
    let ⟨ip2, pT2, K2, η2, η2_j⟩ <- eG.get_rep wf T2
    let p1n <- eG.nodes[ip1]?
    let p2n <- eG.nodes[ip2]?
    if h : ip1 == ip2 && pT1 == pT2 && K == K1 && K1 == K2
    then  -- same class
      let ⟨symm_η2, j2'⟩ := EqGraph.symm (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) η2 K2 T2 pT2 η2_j
      let ⟨symm_η2_η1, j⟩ := EqGraph.seq (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) η1 symm_η2 K1 T1 pT1 T2 η1_j
          (by simp at h; rcases h with ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩; subst e4; subst e3; subst e2; apply j2')
      return ⟨symm_η2_η1, by simp at h; rcases h with ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩; subst e4; subst e3; subst e2; apply j⟩
    else  -- different class
      none
  | _, _ => none


def EqGraph.process_ty {G : GlobalEnv} {Δ : KindEnv} {Γ : TyEnv} {wf : ⊢ G} (eG : EqGraph G Δ Γ) (t : Term) (T : Ty) : Option (EqGraph G Δ Γ) := do
 match t0h : t.infer_type G Δ Γ with
 | some T' =>
   if he : T == T'
   then
     match h1 : t, h2 : T with
     | t, (T1 ~[K]~ T2) => do
       match t1h : T1.infer_kind G Δ with
       | some K' =>
         match t2h : T2.infer_kind G Δ with
         | some K'' =>
           if h : K' == K'' && K' == K
           then
             have lem0 := infer_type_sound wf t0h
             have lem1 := infer_kind_sound t1h
             have lem2 := infer_kind_sound t2h
             by simp at h; rcases h with ⟨e1, e2⟩;
                subst K'; subst K''
                simp at he; subst he;
                apply eG.process_equation (wf := wf) K T1 lem1 T2 lem2 ⟨t, lem0⟩
           else none
         | none => none
       | none => none
     | _, _ => return eG
   else none
 | none => none

def EqGraph.process_tyenv {G : GlobalEnv} {Δ : KindEnv} {wf : ⊢ G} (Γ : TyEnv): Option (EqGraph G Δ Γ) := (Γ.attach.zip (List.range Γ.length)).foldlM (λ acc (t, i) => process_ty (G := G) (Δ := Δ) (Γ := Γ) (wf := wf) acc #i t.1) EqGraph.empty


end Core.Ppcc

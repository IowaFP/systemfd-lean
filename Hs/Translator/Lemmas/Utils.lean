import Batteries.Data.List
import Hs.Monad

theorem list_empty_length {l : List α} : l.length = 0 -> l = [] := by
  intro h; cases l <;> simp at h; rfl

theorem list_non_empty {l : List α} {n : Nat} : l.length = n + 1 -> ∃ x xs, (x :: xs) = l := by
  intro h; induction l generalizing n <;> simp at *


theorem mapM'_elems  {f : α -> DsM β} {ls : List α} {ls' : List β} :
  List.mapM' f ls = DsM.ok ls' ->
  ∀ a ∈ ls, ∃ a' ∈ ls', f a = DsM.ok a' := by
intro j a aj
induction ls generalizing ls'
case _ => cases aj
case _ ih =>
  simp at aj
  simp at j;
  unfold bind at j;
  rw[Monad.toBind] at j;
  unfold Except.instMonad at j;
  simp at j; cases j; case _ a' j =>
  cases j; case _ j1 j2 =>
  cases aj;
  case _ hd tl aj =>
    cases aj;
    generalize fah : f a = fa at *
    generalize mtlh : List.mapM' f tl = mtl at *
    exists a';
    constructor
    case _ =>
      unfold Except.map at j2;
      cases mtl <;> simp at j2
      rw[<-j2]; simp;
    assumption
  case _ hd tl h =>
    unfold Except.map at j2
    generalize mtlh : List.mapM' f tl = mtl at *
    cases mtl <;> simp at j2
    case _ tl' =>
      have ih' := ih rfl h;
      rw[<-j2]
      simp at ih';
      cases ih';
      case _ a' ih' =>
      exists a';
      cases ih';
      constructor;
      simp; apply Or.inr; assumption
      assumption


theorem mapM'_elems_image {f : α -> DsM β} {ls : List α} {ls' : List β} :
  List.mapM' f ls = DsM.ok ls' ->
  ∀ a' ∈ ls', ∃ a ∈ ls, f a = DsM.ok a' := by
intro j a aj
induction ls using List.mapM'.induct generalizing ls' f <;> simp
case _ => cases j; simp at aj
case _ ih =>
  simp at j; unfold bind at j; unfold Monad.toBind at j; unfold Except.instMonad at j; simp at j
  cases j; case _ w j =>
  cases j; case _ j1 j2 =>
  unfold Except.map at j2;
  split at j2 <;> cases j2
  case _ =>
    simp at aj; cases aj
    case _ aj => cases aj; apply Or.inl; assumption
    case _ h aj => replace ih := ih h aj; apply Or.inr; assumption


theorem mapM'_elems_length (ls : List α) (ls' : List β) (f : α -> DsM β) :
  List.mapM' f ls = DsM.ok ls'->
  ls.length = ls'.length := by
intro h
induction ls generalizing ls'
case _ =>
  simp at h;
  unfold pure at h; unfold Applicative.toPure at h; unfold Monad.toApplicative at h;
  unfold Except.instMonad at h; simp at h; unfold Except.pure at h; simp at h; rw[h]; simp
case _ hd tl ih =>
  simp at h; unfold bind at h; unfold Monad.toBind at h; unfold Except.instMonad at h; simp at h;
  cases h;
  case _ hd' h =>
  cases h; case _ h1 h2 =>
  simp at h2; unfold Except.map at h2;
  generalize tlh : List.mapM' f tl = tl' at *;
  cases tl'
  case _ => simp at h2
  case _ tl' =>
  simp at h2;
  have ih := ih tl' (by simp); rw[<-h2]; simp; assumption

theorem mapM'_elems_shape (ls : List α) (ls' : List β) (f : α -> DsM β) :
  ls = hd1 :: ls1 ->
  List.mapM' f ls = DsM.ok ls' ->
  ∃ hd1' ls1', f hd1 = .ok hd1' ∧ List.mapM' f ls1 = .ok ls1' ∧ ls' = hd1' :: ls1' := by
 intro e h
 induction ls generalizing ls'
 case _ => cases e
 case _ hd tl ih =>
 rw [e] at h;
 simp at h; unfold bind at h; unfold Monad.toBind at h; unfold Except.instMonad at h; simp at h;
 cases h; case _ w h =>
 cases h; case _ h =>
 unfold Except.map at h;
 generalize lsh : List.mapM' f ls1 = ls1' at *
 cases ls1' <;> simp at h
 case _ ls1' =>
   cases e
   exists w; exists ls1'
   constructor; assumption
   constructor
   simp
   symm at h; assumption

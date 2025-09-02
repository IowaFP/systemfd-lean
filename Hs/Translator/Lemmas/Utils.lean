import Batteries.Data.List
import Hs.Monad

theorem list_empty_length (l : List α) : l.length = 0 -> l = [] := by
intro h
cases l <;> simp at h
rfl


theorem mapM'_elems (ls : List α) (ls' : List β) (f : α -> DsM β) :
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
      have ih' := ih tl' rfl h;
      rw[<-j2]
      simp at ih';
      cases ih';
      case _ a' ih' =>
      exists a';
      cases ih';
      constructor;
      simp; apply Or.inr; assumption
      assumption

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


theorem mapM'_elems_idx (ls : List α) (ls' : List β) (f : α -> DsM β) :
  List.mapM' f ls = DsM.ok ls' ->
  ∀ i : Nat, ls[i]? = .some a ->
  ls'[i]? = .some a' ->
  f a = DsM.ok a' := by
intro j i j1 j2
induction ls <;> simp at *
case _ hd tl ih =>
 unfold bind at j; rw[Monad.toBind] at j; unfold Except.instMonad at j; simp at j
 cases j; case _ a' j =>
 cases j; case _ e j =>
 unfold Except.map at j
 generalize mtlh : List.mapM' f tl = mtl at *
 induction mtl <;> simp at j
 sorry

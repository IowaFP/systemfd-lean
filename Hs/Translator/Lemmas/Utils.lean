import Batteries.Data.List
import Hs.Monad

theorem forget_attach {κs : List α} {sp : List (β1 × β2)} {f : α -> β2 -> DsM γ} :
 List.mapM (fun arg => f arg.val.fst.val arg.val.snd.val.snd) (κs.attach.zip sp.attach).attach = Except.ok sp_τs ->
 List.mapM (fun arg => f arg.fst arg.snd.snd) (κs.zip sp) = Except.ok sp_τs
    := by
 intro j
 induction κs generalizing sp sp_τs <;> simp at *
 assumption
 induction sp <;> (simp at *; unfold List.zip at j; unfold List.attach at j; simp at j)
 case _ => assumption
 case _ =>
   unfold bind at *; rw[Monad.toBind] at *; unfold Except.instMonad at *; simp at *;
   cases j; case _ a' j =>
   exists a'
   cases j; case _ j1 j2 =>
   constructor
   assumption
   simp at j2;

   sorry



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

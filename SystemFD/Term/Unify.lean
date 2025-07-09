import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Term.Equality

abbrev Unifiable (A : Term) (B : Term) := ∃ σ, ([σ] A = [σ] B)


-- abbrev AgreeableSubsts (σ1 : Subst Term) (σ2 : Subst Term) := σ1 ⊙ σ2

-- Supposed to compute the most general unifier
@[simp]
def unify : Term -> Term -> Option (Subst Term)
| (.var x) , t =>  -- do occurs check? x ∉ fvs t
  .some (λ i => .su (if i == x then t else .var i))
| (.ctor1 v1 t1), (.ctor1 v2 t1') => if v1 == v2 then unify t1 t1' else .none
| (.ctor2 v1 t1 t2), (.ctor2 v2 t1' t2') =>
  if v1 == v2
  then do
  let σ1 <- unify t1 t1'
  let σ2 <- unify t2 t2'
  -- need a way to say something about σ1 and σ2 are consistent
  .some (σ2 ⊙ σ1)
  else .none
| _,_ => .none

theorem unify_sound : unify A B = .some σ -> Unifiable A B := by
intro j
induction A, B using unify.induct generalizing σ <;> (unfold Unifiable)
case _ =>
  simp at j; exists σ; simp;rw[<-j]; simp;
  sorry -- simp at j; exists σ; rw[<-j]; simp
case _ ih =>
  replace ih := ih j;
  unfold Unifiable at ih; cases ih; case _ σ ih =>
  exists σ; simp; assumption
case _ h => simp at h
case _ v1 _ _ v2 _ _ h ih1 ih2 =>
  unfold unify at j; rw[<-h] at j; simp at j;
  rw[Option.bind_eq_some] at j;
  cases j; case _ σ1 j =>
  rw[Option.bind_eq_some] at j;
  cases j; case _ σh1 j =>
  cases j; case _ σ2 j =>
  cases j; case _ σh2 j =>

  replace ih1 := ih1 σh1
  replace ih2 := ih2 σh2

  exists (σ2 ⊙ σ1); -- do MGU's compose?
  simp;
  constructor;
  apply @LawfulBEq.eq_of_beq Ctor2Variant _ _ v1 v2; assumption
  sorry

case _ h => unfold unify at j; sorry
case _ => simp at j

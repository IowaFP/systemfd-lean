import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Util

inductive SpineVariant where
| term | type | kind
 deriving Repr

namespace SpineVariant
  @[simp]
  def beq : SpineVariant -> SpineVariant -> Bool
  | term, term => true
  | type, type => true
  | kind, kind => true
  | _, _ => false
end SpineVariant

@[simp]
instance instBEq_SpineVariant : BEq SpineVariant where
  beq := SpineVariant.beq

instance instLawfulBEq_SpineVariant : LawfulBEq SpineVariant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp

namespace Term
  @[simp]
  def neutral_form : Term -> Option (Nat × List (SpineVariant × Term))
  | var x => .some (x, [])
  | ctor2 .app f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.term, a)])
  | ctor2 .appt f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.type, a)])
  | ctor2 .appk f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.kind, a)])
  | _ => .none

  @[simp]
  def apply_spine : Term -> List (SpineVariant × Term) -> Term
  | t, [] => t
  | t, .cons (.term, h) tl => apply_spine (t `@ h) tl
  | t, .cons (.type, h) tl => apply_spine (t `@t h) tl
  | t, .cons (.kind, h) tl => apply_spine (t `@k h) tl

  theorem apply_spine_peel_term :
    apply_spine f (sp ++ [(.term, a)]) = (apply_spine f sp `@ a)
  := by
  induction f, sp using apply_spine.induct <;> simp
  all_goals (case _ ih => rw [ih])

  theorem apply_spine_peel_type :
    apply_spine f (sp ++ [(.type, a)]) = (apply_spine f sp `@t a)
  := by
  induction f, sp using apply_spine.induct <;> simp
  all_goals (case _ ih => rw [ih])

  theorem apply_spine_peel_kind :
    apply_spine f (sp ++ [(.kind, a)]) = (apply_spine f sp `@k a)
  := by
  induction f, sp using apply_spine.induct <;> simp
  all_goals (case _ ih => rw [ih])

  theorem var_neutral_form : (#n).neutral_form = .some (n, []) := by
  unfold Term.neutral_form; rfl

  theorem neutral_form_app:
  f.neutral_form = .some (h, sp) ->
  (f `@ t).neutral_form = .some (h, sp ++ [(.term, t)]) := by
  intros h; simp_all

  theorem neutral_form_appt:
  f.neutral_form = .some (h, sp) ->
  (f `@t t).neutral_form = .some (h, sp ++ [(.type, t)])
  := by intros h; simp_all

  theorem neutral_form_appk:
  f.neutral_form = .some (h, sp) ->
  (f `@k t).neutral_form = .some (h, sp ++ [(.kind, t)])
  := by intros h; simp_all

  theorem unique_neutral_form : (Term.neutral_form t = .some (n, sp))
                            -> (Term.neutral_form t = .some (n', sp')) -> (n = n' ∧ sp = sp') := by
  intros tnf tnf';
  induction t using Term.neutral_form.induct;
  any_goals (solve | simp_all)

  theorem neutral_form_app_rev:
  (f `@ t).neutral_form = .some (h, sp ++ [(.term, t)] ) ->
  f.neutral_form = .some (h, sp) := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;

  theorem neutral_form_appk_rev_exists:
  (f `@k t).neutral_form = .some (h, sp) ->
  ∃ sp', f.neutral_form = .some (h, sp') ∧ sp = sp' ++ [(.kind , t)] := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;



  theorem neutral_form_appt_rev:
  (f `@t t).neutral_form = .some (h, sp ++ [(.type, t)] ) ->
  f.neutral_form = .some (h, sp) := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;

  theorem apply_spine_compose :
    Term.apply_spine t (t1 ++ t2) = Term.apply_spine (Term.apply_spine t t1) t2
  := by
  induction t, t1 using Term.apply_spine.induct generalizing t2
  case _ => simp
  all_goals (case _ ih => simp; rw [ih])

  theorem neutral_form_law :
    .some (x, sp) = Term.neutral_form t ->
    Term.apply_spine #x sp = t
  := by
  intro h; induction t using neutral_form.induct generalizing x sp
  case _ =>
    simp at h; cases h; case _ h1 h2 =>
      subst h1; subst h2; simp
  case _ ih =>
    simp at h; replace h := Eq.symm h
    rw [Option.bind_eq_some] at h; simp at h
    cases h; case _ a h =>
    cases h; case _ b h =>
    cases h; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3
      replace ih := ih (Eq.symm h1)
      rw [apply_spine_peel_term, ih]
  case _ ih =>
    simp at h; replace h := Eq.symm h
    rw [Option.bind_eq_some] at h; simp at h
    cases h; case _ a h =>
    cases h; case _ b h =>
    cases h; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3
      replace ih := ih (Eq.symm h1)
      rw [apply_spine_peel_type, ih]
  case _ ih =>
    simp at h; replace h := Eq.symm h
    rw [Option.bind_eq_some] at h; simp at h
    cases h; case _ a h =>
    cases h; case _ b h =>
    cases h; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
      subst h2; subst h3
      replace ih := ih (Eq.symm h1)
      rw [apply_spine_peel_kind, ih]
  case _ h1 h2 h3 h4 => simp at h

  @[simp]
  def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
  | var x =>
    match f x with
    | .re y => var y
    | .su t => t
  | kind => kind
  | type => type
  | ctor1 v t => ctor1 v (smap lf f t)
  | ctor2 v t1 t2 => ctor2 v (smap lf f t1) (smap lf f t2)
  | bind2 v t1 t2 => bind2 v (smap lf f t1) (smap lf (lf f) t2)
  | ite t1 t2 t3 t4 => ite (smap lf f t1) (smap lf f t2) (smap lf f t3) (smap lf f t4)
  | guard t1 t2 t3 => guard (smap lf f t1) (smap lf f t2) (smap lf f t3)
  | letterm t1 t2 t3 => letterm (smap lf f t1) (smap lf f t2) (smap lf (lf f) t3)
end Term

@[simp]
instance substType_Term : SubstitutionType Term where
  smap := Term.smap

namespace Term
  @[simp↓]
  theorem subst_var : [σ](Term.var x) = match σ x with | .re y => .var y | .su t => t := by
  unfold Subst.apply; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_replace
    : [.su s :: σ](var 0) = s
  := by simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_var_rename
    : [.re k :: σ](var 0) = var k
  := by simp

  @[simp]
  theorem subst_kind : [σ]kind = kind := by unfold Subst.apply; simp

  @[simp]
  theorem subst_const : [σ]type = type := by unfold Subst.apply; simp

  @[simp]
  theorem subst_ite : [σ]ite t1 t2 t3 t4 = ite ([σ]t1) ([σ]t2) ([σ]t3) ([σ]t4) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_guard : [σ]guard t1 t2 t3 = guard ([σ]t1) ([σ]t2) ([σ]t3) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_ctor1 : [σ]ctor1 v t = ctor1 v ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_ctor2 : [σ]ctor2 v t1 t2 = ctor2 v ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_bind2 : [σ]bind2 v t1 t2 = bind2 v ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letterm: [σ]letterm t1 t2 t3 = letterm ([σ]t1) ([σ]t2) ([^σ]t3) := by unfold Subst.apply; simp


  theorem apply_id {t : Term} : [I]t = t := by
  have lem1 : ^I = @I Term := by
    funext; case _ x =>
    cases x; all_goals (unfold Subst.lift; unfold I; simp)
  induction t
  all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst Term}
    : r.to = σ -> Ren.apply r = Subst.apply σ
  := by
  intro h; funext; case _ x =>
    unfold Ren.apply; simp at *
    unfold Ren.to; simp
    induction x generalizing r σ <;> simp at *
    case _ x => rw [<-h]; unfold Ren.to; simp
    all_goals simp [*]
    all_goals (
      rw [Subst.lift_lemma, <-h]
      unfold Ren.fro; simp
    )

  theorem apply_compose {s : Term} {σ τ : Subst Term} : [τ][σ]s = [τ ⊙ σ]s := by
  solve_compose Term, apply_stable, s, σ, τ

  @[simp]
  def to_telescope : Term -> Ctx Term × Term
  | bind2 .arrow A B =>
    let (Γ, r) := to_telescope (B)
    (.type A::Γ, r)
  | ∀[A] B =>
    let (Γ, r) := to_telescope (B)
    (.kind A::Γ, r)
  | t => ([], t)

  @[simp]
  def from_telescope_rev : Ctx Term -> Term -> Term
  | [], t => t
  | .cons (.type A) Γ, t => from_telescope_rev Γ (.bind2 .arrow A t)
  | .cons (.kind A) Γ, t => from_telescope_rev Γ (∀[A] t)
  | .cons _ Γ, t => from_telescope_rev Γ t

  @[simp]
  def from_telescope (Γ : Ctx Term) (t : Term) : Term :=
    from_telescope_rev Γ.reverse t

end Term

instance substTypeLaws_Term : SubstitutionTypeLaws Term where
  apply_id := Term.apply_id
  apply_compose := Term.apply_compose
  apply_stable := Term.apply_stable

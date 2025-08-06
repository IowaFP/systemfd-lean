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


  -- k1 `-k> k2 `-k> k3 -→ [k1, k2, k3]
  @[simp]
  def split_kind_arrow_aux : List Term -> Term -> Option (List Term × Term)
  | Γ, .ctor2 .arrowk f a => split_kind_arrow_aux (f :: Γ) a
  | Γ, ★ => .some (Γ, ★)
  | _, _ => .none

  @[simp]
  def split_kind_arrow : Term -> Option (List Term × Term) := split_kind_arrow_aux []

  @[simp]
  def mk_kind_arrow ( base : Term) : List Term -> Term
  | [] => base
  | .cons k ks => k -k> (mk_kind_arrow base ks)

  theorem kind_arrow_lemma : split_kind_arrow κ = .some (κs, ret_κ) ->
      mk_kind_arrow ret_κ κs = κ := by
  intros h
  induction κs generalizing κ ret_κ <;> simp at *
  induction κ <;> simp at *
  cases h; rfl
  sorry
  sorry

  @[simp]
  def mk_kind_app : Nat -> List Term -> Term := λ h sp =>
    List.foldl (λ acc a => acc `@k a) (#h) sp

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
    (f `@ t).neutral_form = .some (h, sp ++ [(.term, t)])
  := by
  intros h; simp_all

  theorem neutral_form_appt:
    f.neutral_form = .some (h, sp) ->
    (f `@t t).neutral_form = .some (h, sp ++ [(.type, t)])
  := by intros h; simp_all

  theorem neutral_form_appk:
    f.neutral_form = .some (h, sp) ->
    (f `@k t).neutral_form = .some (h, sp ++ [(.kind, t)])
  := by intros h; simp_all

  theorem unique_neutral_form :
    (Term.neutral_form t = .some (n, sp)) ->
    (Term.neutral_form t = .some (n', sp')) ->
    (n = n' ∧ sp = sp')
  := by
  intros tnf tnf';
  induction t using Term.neutral_form.induct;
  any_goals (solve | simp_all)

  theorem neutral_form_app_rev:
    (f `@ t).neutral_form = .some (h, sp ++ [(.term, t)] ) ->
    f.neutral_form = .some (h, sp)
  := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;

  theorem neutral_form_appk_rev_exists:
    (f `@k t).neutral_form = .some (h, sp) ->
    ∃ sp', f.neutral_form = .some (h, sp') ∧ sp = sp' ++ [(.kind , t)]
  := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;

  theorem neutral_form_appt_rev:
    (f `@t t).neutral_form = .some (h, sp ++ [(.type, t)] ) ->
    f.neutral_form = .some (h, sp)
  := by
  intros h; simp_all;
  case _ n =>
  rw [Option.bind_eq_some] at h; cases h; case _ w h =>
  simp at h; have h2 := h.2.1; have h3 := h.2.2;
  subst h2; subst h3; simp_all;

  theorem neutral_form_bind2 : (Term.bind2 a1 a2 a3).neutral_form = .none := by
  unfold Term.neutral_form; rfl

  theorem neutral_form_ctor1 : (Term.ctor1 a1 a2).neutral_form = .none := by
  unfold Term.neutral_form; rfl

  theorem neutral_form_ite : (Term.ite p s i e).neutral_form = .none := by
  unfold Term.neutral_form; rfl

  theorem neutral_form_guard : (Term.guard p s e).neutral_form = .none := by
  unfold Term.neutral_form; rfl

  theorem neutral_form_letterm : (Term.letterm a1 a2 a3).neutral_form = .none := by
  unfold Term.neutral_form; rfl

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
  | zero => zero
  | kind => kind
  | type => type
  | ctor1 v t => ctor1 v (smap lf f t)
  | ctor2 v t1 t2 => ctor2 v (smap lf f t1) (smap lf f t2)
  | bind2 v t1 t2 => bind2 v (smap lf f t1) (smap lf (lf f) t2)
  | eq t1 t2 t3 => eq (smap lf f t1) (smap lf f t2) (smap lf f t3)
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
  theorem subst_zero : [σ]zero = zero := by unfold Subst.apply; simp

  @[simp]
  theorem subst_eq : [σ]eq t1 t2 t3 = eq ([σ]t1) ([σ]t2) ([σ]t3) := by unfold Subst.apply; simp

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
    let (Γ, r) := to_telescope B
    (.type A::Γ, r)
  | ∀[A] B =>
    let (Γ, r) := to_telescope B
    (.kind A::Γ, r)
  | t => ([], t)

  @[simp]
  def to_telescope_head : Term -> Option (Frame Term × Term)
  | bind2 .arrow A B =>
    .some (.type A, B)
  | ∀[A] B => .some (.kind A, B)
  | ∀c[A] B => .some (.kind A, B)
  | _ => .none

  @[simp]
  def from_telescope_rev : Ctx Term -> Term -> Term
  | [], t => t
  | .cons (.type A) Γ, t => from_telescope_rev Γ (.bind2 .arrow A t)
  | .cons (.kind A) Γ, t => from_telescope_rev Γ (∀[A] t)
  | .cons _ Γ, t => from_telescope_rev Γ t

  @[simp]
  def from_telescope (Γ : Ctx Term) (t : Term) : Term :=
    from_telescope_rev Γ.reverse t

  theorem telescope_neutral_form_lemma {t : Term} :
    t.neutral_form = .some (x, xs) ->
    t.to_telescope = ([], t) := by
    induction t;
    any_goals (solve | simp_all)

  theorem unique_telescope {t : Term} :
    t.to_telescope = (x, xs) ->
    t.to_telescope = (x', xs') ->
    x = x' ∧ xs = xs' :=  by
    intros h1 h2; rw [h1] at h2; simp at h2; assumption;


   @[simp]
   def shift_helper_aux : Nat -> List Nat -> List Nat
   | 0, acc => acc
   | n + 1, acc => shift_helper_aux n (n :: acc)

   @[simp]
   def shift_helper : Nat -> List Nat := λ n => shift_helper_aux n []

   @[simp]
   def mk_eqs : List (Term × Term × Term) -> List Term := List.map (λ x => x.2.1 ~[x.1]~ x.2.2)

   @[simp]
   def mk_type_telescope : Ctx Term -> List Term -> Ctx Term := λ Γ ts =>
     List.foldl (λ Γ t_data =>
       let t := t_data.2
       let shift := t_data.1
       (.type ([S' shift] t) :: Γ)
     ) Γ (List.zip (shift_helper ts.length) ts)

   @[simp]
   def mk_kind_telescope : Ctx Term -> List Term -> Ctx Term := λ Γ ts =>
     List.foldl (λ Γ t_data =>
       let t := t_data.2
       let shift := t_data.1
       (.kind ([S' shift] t) :: Γ)
     ) Γ (List.zip (shift_helper ts.length) ts)

   @[simp]
   def mk_kind_apps : Term -> List Term -> Term := λ h args =>
     List.foldl (λ acc a => acc `@k a) h args

   @[simp]
   def mk_kind_apps_rev : Term -> List Term -> Term
   | t, [] => t
   | t, .cons a args => (mk_kind_apps_rev t args) `@k a

   @[simp]
   def mk_ty_apps : Term -> List Term -> Term := λ h args =>
     List.foldl (λ acc a => acc `@t a) h args

   @[simp]
   def mk_ty_apps_rev : Term -> List Term -> Term
   | t, [] => t
   | t, .cons a args => (mk_ty_apps_rev t args) `@t a


   @[simp]
   def mk_apps : Term -> List Term -> Term := λ h args =>
     List.foldl (λ acc a => acc `@ a) h args

   @[simp]
   def mk_apps_rev : Term -> List Term -> Term
   | t, [] => t
   | t, .cons a args => (mk_apps_rev t args) `@ a

   @[simp]
   def mk_lams : Term -> Ctx Term -> Option Term
   | t, [] => t
   | t, .cons (.kind x) xs => do
     let t' <- (mk_lams t xs)
     .some (Λ[x] t')
   | t, .cons (.type x) xs => do
     let t' <- (mk_lams t xs)
     .some (`λ[x] t')
   | _, _ => .none


   @[simp]
   def mk_lams_rev : Term -> Ctx Term -> Option Term
   | t, [] => .some t
   | t, .cons (.kind x) xs =>
     mk_lams_rev (Λ[x] t) xs
   | t, .cons (.type x) xs =>
     mk_lams_rev (`λ[x] t) xs
   | _, _ => .none


  @[simp] -- TODO replace uses with from_telescope?
  def mk_arrow : Term -> Ctx Term -> Option Term
  | t, [] => .some t
  | t, .cons (.kind x) xs => do
    let t' <- mk_arrow t xs
    .some (∀[x] t')
  | t, .cons (.type x) xs => do
    let t' <- mk_arrow  t xs
    .some (x -t> t')
  | _, _ => .none

  @[simp] -- TODO replace uses with from_telescope?
  def mk_arrow_rev : Term -> Ctx Term -> Option Term
  | t, [] => .some t
  | t, .cons (.type x) xs => do
    mk_arrow_rev (x -t> t) xs
  | t, .cons (.kind x) xs => do
    mk_arrow_rev (∀[x] t) xs
  | _, _ => .none


   @[simp]
   def mk_lets : Term -> Ctx Term -> Option Term
   | t, [] => t
   | t, .cons (.term A x) xs => do
     let t' <- (mk_lets t xs)
     .some (.letterm A x t')
   | _, _ => .none

   @[simp]
   def mk_lets_rev : Term -> Ctx Term -> Option Term
   | t, [] => .some t
   | t, .cons (.term A x) xs =>
     mk_lets_rev (.letterm A x t) xs
   | _, _ => .none

end Term

instance substTypeLaws_Term : SubstitutionTypeLaws Term where
  apply_id := Term.apply_id
  apply_compose := Term.apply_compose
  apply_stable := Term.apply_stable

  @[simp]
  theorem size_of_subst_rename {t : Term} (r : Ren)
    : Term.size ([r.to]t) = Term.size t
  := by
  have lem (r : Ren) :
    .re 0::((@S Term) ⊙ r.to) = (Subst.size_of_subst_rename_renamer r).to
  := by
    unfold Ren.to; simp
    funext; case _ x =>
      cases x <;> simp
      case _ n => unfold Subst.compose; simp
  induction t generalizing r <;> simp [*]
  case _ x => unfold Ren.to; simp

  theorem right_shifting_size_no_change (s : Term) : s.size = ([S' k]s).size := by
  have lem := @size_of_subst_rename s (fun n => n + k);
  unfold S'; rw [<-lem]; rfl

  theorem right_shifting_size_no_change1 {s : Term} : s.size = ([S]s).size := by
  have lem := @right_shifting_size_no_change 1 s;
  unfold S; unfold S' at lem; assumption

  theorem left_shifting_size_no_change {s : Term} : s.size = ([P' k]s).size := by
  have lem := @size_of_subst_rename s (fun n => n - k);
  unfold P'; rw [<-lem]; rfl

  theorem left_shifting_size_no_change1 {s : Term} : s.size = ([P]s).size := by
  have lem := @left_shifting_size_no_change 1 s;
  unfold P; unfold P' at lem; assumption

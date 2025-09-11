import SystemFD.Substitution
import Hs.HsCtx
import Hs.HsTerm.Definition
import SystemFD.Util


inductive HsSpineVariant where
| term | kind | type
deriving Repr

namespace HsSpineVariant
  @[simp]
  def beq : HsSpineVariant -> HsSpineVariant -> Bool
  | .term, .term => true
  | .kind, .kind => true
  | .type, .type => true
  | _, _ => false
end HsSpineVariant

@[simp]
instance instBEq_HsSpineVariant : BEq HsSpineVariant where
  beq := HsSpineVariant.beq

instance instLawfulBEq_HsSpineVariant : LawfulBEq HsSpineVariant where
  eq_of_beq := by
    intro a b h; simp at h
    cases a <;> cases b <;> simp at *
  rfl := by
    intro a; simp
    cases a <;> simp


namespace HsTerm
  @[simp]
  def neutral_form : HsTerm -> Option (HsTerm × List (HsSpineVariant × HsTerm)) -- TODO make more efficient?
  | .HsAnnotate τ x => .some (.HsAnnotate τ x, [])
  | .HsVar x => .some (HsVar x, [])
  | .HsCtor2 .app f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.term, a)])
  | .HsCtor2 .appk f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.kind, a)])
  | .HsCtor2 .appt f a => do
    let (x, sp) <- neutral_form f
    .some (x, sp ++ [(.type, a)])
  | _ => .none

  @[simp]
  def apply_spine (t : HsTerm) (args : List (HsSpineVariant × HsTerm)) : HsTerm
    := List.foldr (λ a acc => match a with
                     | (.term, h) => acc `• h
                     | (.kind, h) => acc `•k  h
                     | (.type, h) => acc `•t h) t args.reverse


  -- Splits #0 `@k t1 `@k t2 --> (0, [t1, t2])
  @[simp]
  def split_kind_app : HsTerm -> Option (Nat × List HsTerm)
  | .HsCtor2 .appk f a => do
    let (f', args) <- split_kind_app f
    .some (f', (args ++ [a]))
  | `#x => .some (x, [])
  | _ => .none

  @[simp]
  def mk_kind_apps' (h : HsTerm) (args : List HsTerm):=  List.foldr (λ a acc => acc `•k a) h args

  @[simp]
  def mk_kind_apps : HsTerm -> List HsTerm -> HsTerm := λ h args => mk_kind_apps' h args.reverse


  theorem apply_spine_peel_term :
    apply_spine f (sp ++ [(.term, a)]) = (apply_spine f sp `• a)
  := by
  induction sp using List.foldr.induct <;> simp
  all_goals (case _ ih => rw [ih])

  theorem apply_spine_peel_type :
    apply_spine f (sp ++ [(.type, a)]) = (apply_spine f sp `•t a)
  := by
  induction sp using List.foldr.induct <;> simp
  all_goals (case _ ih => rw [ih])

  theorem apply_spine_peel_kind :
    apply_spine f (sp ++ [(.kind, a)]) = (apply_spine f sp `•k a)
  := by
  induction sp using List.foldr.induct <;> simp
  all_goals (case _ ih => rw [ih])


  theorem apply_spine_compose :
    HsTerm.apply_spine t (t1 ++ t2) = HsTerm.apply_spine (HsTerm.apply_spine t t1) t2
  := by
  induction t1 using List.foldr.induct generalizing t2
  case _ => simp
  all_goals (case _ ih => simp)

  theorem neutral_form_law :
    .some (`#x, sp) = HsTerm.neutral_form t ->
    HsTerm.apply_spine `#x sp = t
  := by
  intro h; induction t using neutral_form.induct generalizing x sp
  case _ =>
    simp at h
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
      rw [@HsTerm.apply_spine_peel_kind, ih]
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
  case _ h1 h2 h3 h4 => simp at h


  @[simp]
  def smap (lf : Subst.Lift HsTerm) (f : Nat -> Subst.Action HsTerm) : HsTerm -> HsTerm
  | HsVar x =>
    match f x with
    | .re y => HsVar y
    | .su t => t
  | HsName x => HsName x
  | HsKind => HsKind
  | HsType => HsType
  | HsHole t1 => HsHole (smap lf f t1)
  | HsAnnotate t1 t2 => HsAnnotate (smap lf f t1) (smap lf f t2)
  | HsCtor2 v t1 t2 => HsCtor2 v (smap lf f t1) (smap lf f t2)
  | HsBind2 v t1 t2 => HsBind2 v (smap lf f t1) (smap lf (lf f) t2)
  | HsIte t1 t2 t3 t4 => .HsIte (smap lf f t1) (smap lf f t2) (smap lf f t3) (smap lf f t4)
  | HsLet t1 t2 t3 => HsLet (smap lf f t1) (smap lf f t2) (smap lf (lf f) t3)
end HsTerm

@[simp]
instance substType_HsTerm : SubstitutionType HsTerm where
  smap := HsTerm.smap

namespace HsTerm
  @[simp↓]
  theorem subst_var : [σ](HsTerm.HsVar x) = match σ x with | .re y => .HsVar y | .su t => t := by
  unfold Subst.apply; simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_HsVar_replace
    : [.su s :: σ](HsVar 0) = s
  := by simp

  @[simp] -- 0[s.σ ] = s
  theorem subst_HsVar_rename
    : [.re k :: σ](HsVar 0) = HsVar k
  := by simp

  @[simp]
  theorem subst_HsKind : [σ]`□ = `□ := by unfold Subst.apply; simp

  @[simp]
  theorem subst_const : [σ]`★ = `★ := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsName : [σ]HsName x = HsName x := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsIte : [σ]HsIte t1 t2 t3 t4 = HsIte ([σ]t1) ([σ]t2) ([σ]t3) ([σ]t4) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsAnnotate : [σ]HsAnnotate t1 t2 = HsAnnotate ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsHole : [σ]HsHole t1 = HsHole ([σ]t1) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsCtor2 : [σ]HsCtor2 v t1 t2 = HsCtor2 v ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_HsBind2 : [σ]HsBind2 v t1 t2 = HsBind2 v ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letterm: [σ]HsLet t1 t2 t3 = HsLet ([σ]t1) ([σ]t2) ([^σ]t3) := by unfold Subst.apply; simp


  theorem apply_id {t : HsTerm} : [I]t = t := by
  have lem1 : ^I = @I HsTerm := by
    funext; case _ x =>
    cases x; all_goals (unfold Subst.lift; unfold I; simp)
  induction t
  all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst HsTerm}
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

  theorem apply_compose {s : HsTerm} {σ τ : Subst HsTerm} : [τ][σ]s = [τ ⊙ σ]s := by
  solve_compose HsTerm, apply_stable, s, σ, τ

end HsTerm

instance substTypeLaws_HsTerm : SubstitutionTypeLaws HsTerm where
  apply_id := HsTerm.apply_id
  apply_compose := HsTerm.apply_compose
  apply_stable := HsTerm.apply_stable

  @[simp]
  theorem hs_term_size_of_subst_rename {t : HsTerm} (r : Ren)
    : HsTerm.size ([r.to]t) = HsTerm.size t
  := by
  have lem (r : Ren) :
    .re 0::((@S HsTerm) ⊙ r.to) = (Subst.size_of_subst_rename_renamer r).to
  := by
    unfold Ren.to; simp
    funext; case _ x =>
      cases x <;> simp
      case _ n => unfold Subst.compose; simp
  induction t generalizing r <;> simp [*]
  case _ x => unfold Ren.to; simp

  theorem hs_term_right_shifting_size_no_change {s : HsTerm} : s.size = ([S' k]s).size := by
  have lem := @hs_term_size_of_subst_rename s (fun n => n + k);
  unfold S'; rw [<-lem]; rfl

  theorem hs_term_right_shifting_size_no_change1 {s : HsTerm} : s.size = ([S]s).size := by
  have lem := @hs_term_right_shifting_size_no_change 1 s;
  unfold S; unfold S' at lem; assumption

  theorem hs_term_left_shifting_size_no_change {s : HsTerm} : s.size = ([P' k]s).size := by
  have lem := @hs_term_size_of_subst_rename s (fun n => n - k);
  unfold P'; rw [<-lem]; rfl

  theorem hs_term_left_shifting_size_no_change1 {s : HsTerm} : s.size = ([P]s).size := by
  have lem := @hs_term_left_shifting_size_no_change 1 s;
  unfold P; unfold P' at lem; assumption

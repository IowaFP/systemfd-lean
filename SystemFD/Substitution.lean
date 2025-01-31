
def Ren : Type := Nat -> Nat

namespace Subst
  inductive Action (T : Type) : Type where
  | re : Nat -> Action T
  | su : T -> Action T

  def Lift (X : Type) : Type := (Nat -> Action X) -> Nat -> Action X
end Subst

def Subst (T : Type) : Type := Nat -> Subst.Action T

class SubstitutionType (T : Type) where
  smap : Subst.Lift T -> (Nat -> Subst.Action T) -> T -> T

def seq_cons : T -> (Nat -> T) -> (Nat -> T)
| t, _, 0 => t
| _, σ, n + 1 => σ n

infix:70 "::" => seq_cons

section
  variable
    {F : Type -> Type}
    {T : Type} [SubstitutionType T]

  open SubstitutionType

  namespace Ren
    def to : Ren -> Subst T
    | r, n => .re (r n)

    def fro : Subst T -> Ren
    | σ, n =>
      match σ n with
      | .su _ => 0
      | .re k => k

    def lift : Ren -> Ren
    | _, 0 => 0
    | σ, n + 1 => σ n + 1

    def apply (r : Ren) : T -> T := smap (to ∘ lift ∘ fro) (to r)
  end Ren

  namespace Subst
    def lift : Subst T -> Subst T
    | _, 0 => .re 0
    | σ, n + 1 => match (σ n) with
      | .su t => .su (Ren.apply (λ n => n + 1) t)
      | .re k => .re (k + 1)

    def apply (σ : Subst T) : T -> T := smap lift σ

    def compose : Subst T -> Subst T -> Subst T
    | σ, τ, n => match (σ n) with
      | .su t => .su (apply τ t)
      | .re k => τ k

    @[simp]
    def betan : Nat -> T -> Subst T
    | x, t, n => if x == n then .su t else .re n

  end Subst

  def I : Subst T := λ n => .re n
  def S : Subst T := λ n => .re (n + 1)
  def P : Subst T := λ n => .re (n - 1)
  def S' (k : Nat) : Subst T := λ n => .re (n + k)

  omit [SubstitutionType T] in
  @[simp]
  theorem I_action : @I T n = .re n := by unfold I; simp

  omit [SubstitutionType T] in
  @[simp]
  theorem S_action : @S T n = .re (n + 1) := by unfold S; simp

  omit [SubstitutionType T] in
  @[simp]
  theorem P_action : @P T n = .re (n - 1) := by unfold P; simp

  prefix:max "^" => Subst.lift
  notation:90 "[" σ "]" t:89 => Subst.apply σ t
  notation:90 τ:90 " ⊙ " σ:91 => Subst.compose σ τ
  notation:90 s:90 "β[" t "]" => Subst.apply ((Subst.Action.su t) :: I) s
  notation:90 s:90 "β[" n ";" t "]" => Subst.apply (Subst.betan n t) s
end

section
  open SubstitutionType
  class SubstitutionTypeLaws (T : Type) [SubstitutionType T] where
    apply_id {t : T} : [I]t = t
    apply_compose {s : T} {σ τ : Subst T} : [τ][σ]s = [τ ⊙ σ]s
    apply_stable {σ : Subst T} : r.to = σ -> Ren.apply r = Subst.apply σ
end

namespace Subst
  @[simp] theorem cons_zero {σ : Subst T} : (s :: σ) 0 = s := by
  unfold seq_cons; simp

  @[simp] theorem cons_succ {σ : Subst T} : (s :: σ) (n + 1) = σ n := by
  unfold seq_cons; simp

section
  variable {T : Type} [SubstitutionType T] [SubstitutionTypeLaws T]

  open SubstitutionType
  open SubstitutionTypeLaws

  omit [SubstitutionTypeLaws T] in
  theorem lift_lemma {r : Ren} :  r.lift.to = ^(@Ren.to T r) := by
  funext; case _ x =>
    cases x
    case zero =>
      unfold Ren.to; unfold Ren.lift; simp
      unfold Subst.lift; simp
    case _ n =>
      generalize lhsdef : ((@Ren.to T r.lift)) (n + 1) = lhs
      generalize rhsdef : (^(@Ren.to T r)) (n + 1) = rhs
      unfold Ren.to at lhsdef; simp at *
      unfold Ren.lift at lhsdef; simp at *
      unfold Subst.lift at rhsdef; simp at *
      subst lhsdef; subst rhsdef; rfl

  @[simp]
  theorem apply_I_is_id {s : T} : [I]s = s :=
    SubstitutionTypeLaws.apply_id

  @[simp]
  theorem apply_compose_commute {s : T} {σ τ : Subst T} : [τ][σ]s = [τ ⊙ σ]s :=
    SubstitutionTypeLaws.apply_compose

  omit [SubstitutionTypeLaws T] in
  @[simp]
  theorem valid1 {s : T} : s β[t] = [.su t :: I]s := by simp

  @[simp] -- ⇑σ = 0.(σ ◦ S)
  theorem valid3 {σ : Subst T} : ^σ = .re 0 :: (S ⊙ σ) := by
  funext; case _ x =>
    cases x
    case _ => unfold Subst.lift; simp
    case _ n =>
      simp; unfold Subst.lift; unfold S; unfold Subst.compose; simp
      generalize tdef : σ n = t
      cases t <;> simp at *
      case _ y =>
        rw [apply_stable]
        funext; case _ i => unfold Ren.to; simp

  omit  [SubstitutionType T] in
  @[simp] -- 0.S = I
  theorem valid4 : .re 0 :: S = @I T := by
  funext; case _ x =>
    cases x; all_goals (unfold seq_cons; unfold S; unfold I; simp)

  omit [SubstitutionTypeLaws T] in
  @[simp] -- σ ◦ I = σ
  theorem valid5 {σ : Subst T} : σ ⊙ I = σ := by
  funext; case _ x =>
    unfold Subst.compose; unfold I; simp

  @[simp] -- I ◦ σ = σ
  theorem valid6 {σ : Subst T} : I ⊙ σ = σ := by
  funext; case _ x =>
    unfold Subst.compose; unfold I; unfold Subst.apply; simp
    generalize zdef : σ x = z
    cases z <;> simp at *
    have lem : smap Subst.lift (λ x => .re x) = @Subst.apply T _ I := by
      unfold Subst.apply; unfold I; simp
    rw [lem, apply_id]

  @[simp] -- (σ ◦ τ) ◦ μ = σ ◦ (τ ◦ μ)
  theorem valid7 {σ : Subst T} : σ ⊙ (τ ⊙ μ) = σ ⊙ τ ⊙ μ := by
  funext; case _ x =>
    unfold Subst.compose; simp
    cases μ x <;> simp
    . unfold Subst.compose; simp

  omit [SubstitutionTypeLaws T] in
  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem valid8_replace {s : T}
    : τ ⊙ (.su s :: σ) = .su ([τ]s) :: (τ ⊙ σ)
  := by
  funext; case _ x =>
    cases x; all_goals (unfold Subst.compose; unfold seq_cons; simp)

  omit [SubstitutionTypeLaws T] in
  @[simp] -- (s.σ ) ◦ τ = s[τ].(σ ◦ τ)
  theorem valid8_rename {σ : Subst T}
    : τ ⊙ (.re s :: σ) = (τ s) :: (τ ⊙ σ)
  := by
  funext; case _ x =>
    cases x; all_goals (unfold Subst.compose; unfold seq_cons; simp)

  omit [SubstitutionTypeLaws T] in
  @[simp] -- S ◦ (s.σ ) = σ
  theorem valid9 {σ : Subst T} : (s :: σ) ⊙ S = σ := by
  funext; case _ x =>
    cases x; all_goals (unfold Subst.compose; unfold seq_cons; unfold S; simp)

  omit [SubstitutionTypeLaws T] in
  @[simp] -- 0[σ ].(S ◦ σ ) = σ
  theorem valid10 {σ : Subst T} : σ 0 :: (σ ⊙ S) = σ := by
  funext; case _ x =>
    cases x
    case _ => simp
    case _ => simp; unfold S; unfold Subst.compose; simp

  omit  [SubstitutionType T] in
  theorem to_S : Ren.to (λ x => x + 1) = @S T := by
  unfold Ren.to; simp; unfold S; simp

  theorem lift_rename {σ τ : Subst T} :
    (∀ n k, σ n = .re k -> τ n = .re k) ->
    ∀ n k, ^σ n = .re k -> ^τ n = .re k
  := by
  intro h1 n k h2
  cases n <;> simp at *
  case _ => exact h2
  case _ n =>
    unfold Subst.compose at *; simp at *
    generalize ydef : σ n = y at *
    cases y <;> simp at *
    case _ i => rw [h1 n i ydef]; simp [*]

  theorem lift_replace
    {R : T -> T -> Prop}
    (Rs : ∀ {t t' : T} σ, R t t' -> R ([σ]t) ([σ]t'))
    {σ τ : Subst T}
  :
    (∀ n t, σ n = .su t -> ∃ t', τ n = .su t' ∧ R t t') ->
    ∀ n t, ^σ n = .su t -> ∃ t', ^τ n = .su t' ∧ R t t'
  := by
  intro h1 n t h2
  cases n <;> simp at *
  case _ n =>
    unfold Subst.compose at h2; simp at h2
    generalize udef : σ n = u at *
    cases u <;> simp at *
    case _ s =>
      replace h1 := h1 n s udef
      unfold Subst.compose; simp
      generalize vdef : τ n = v at *
      cases v <;> simp at *
      case _ w => rw [<-h2]; apply Rs S h1

end

  macro "solve_compose" Ty:term "," apply_stable:term "," s:term "," σ:term "," τ:term : tactic => `(tactic| {
    have lem1 (τ : Subst $Ty) : ^τ ⊙ (Ren.to (λ x => x + 1)) = (Ren.to (λ x => x + 1)) ⊙ τ := by
      funext; unfold Subst.compose; simp; unfold Ren.to; simp; case _ x =>
        generalize zdef : τ x = z; generalize vdef : ^τ (x + 1) = v
        unfold Subst.lift at vdef; simp at vdef; rw [zdef] at vdef
        cases z
        case _ => simp at *; simp [*]
        case _ =>
          simp at *; rw [<-vdef]; simp;
          rw [@$apply_stable (λ x => x + 1) (λ x => .re (x + 1)) (by unfold Ren.to; simp)]
    have lem2 (σ : Subst $Ty) (e : Ren) : ^(σ ⊙ (e.to)) = ^σ ⊙ ^(e.to) := by
      funext; case _ n =>
      cases n
      . unfold Ren.to; unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        generalize lhsdef : (^σ ⊙ ^(e.to)) (n + 1) = lhs
        unfold Subst.lift; simp
        unfold Subst.compose; unfold Ren.to; simp
        subst lhs; unfold Subst.compose; unfold Subst.lift; simp
        unfold Ren.to; simp
    have lem3 {σ : Subst $Ty} {e : Ren} s : [σ][e.to]s = [σ ⊙ (e.to)]s := by
      induction s generalizing σ e
      any_goals simp [*]
      any_goals (rw [<-Subst.lift_lemma]; simp [*])
      any_goals (
        unfold Subst.compose; simp
        unfold Subst.apply; simp; split <;> simp at *
      )
      any_goals (unfold Ren.to; simp [*])
    have lem4 (σ τ : Subst $Ty) : σ ⊙ τ ⊙ (Ren.to (λ x => x + 1)) = σ ⊙ (τ ⊙ (Ren.to (λ x => x + 1))) := by
      funext; case _ x =>
      cases x; any_goals (unfold Subst.compose; unfold Ren.to; simp)
    have lem5 (r1 r2 : Ren) (τ : Subst $Ty) : r1.to ⊙ (r2.to ⊙ τ) = r1.to ⊙ r2.to ⊙ τ := by
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        case _ t =>
          have lem : [fun x => Subst.Action.re (r1 (r2 x))]t = [r1.to ⊙ r2.to]t := by
            unfold Subst.compose; unfold Ren.to; simp
          rw [<-lem3] at lem; unfold Ren.to at lem; simp at lem
          unfold Ren.to; simp; rw [lem]
    have lem6 (e : Ren) (τ : Subst $Ty) : ^(e.to) ⊙ ^τ = ^((e.to) ⊙ τ) := by
      funext; case _ n =>
      cases n
      . unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        have lem : ((^(e.to) ⊙ ^τ) ⊙ (Ren.to (fun x => x + 1))) n = (^(e.to ⊙ τ) ⊙ (Ren.to (fun x => x + 1))) n := by {
          rw [lem1, lem4, lem1]
          rw [<-Subst.lift_lemma, lem5]; simp
          rw [Subst.lift_lemma, lem1, lem5]
        }
        unfold Subst.compose at lem; unfold Ren.to at lem
        unfold Subst.compose; unfold Ren.to
        simp at lem; simp [*]
    have lem7 (τ : Subst $Ty) (e : Ren) s : [e.to][τ]s = [(e.to) ⊙ τ]s := by
      induction s generalizing τ e
      any_goals simp [*]
      any_goals (rw [<-lem6, <-Subst.lift_lemma]; simp [*])
      any_goals (
        unfold Subst.compose; simp
        unfold Subst.apply; simp; split <;> simp [*]
      )
    have lem8 (σ τ : Subst $Ty) : σ ⊙ ((Ren.to (λ x => x + 1)) ⊙ τ) = σ ⊙ (Ren.to (λ x => x + 1)) ⊙ τ := by
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        rw [lem3]; unfold Subst.compose; simp
    have lem9 (σ τ : Subst $Ty) : (Ren.to (λ x => x + 1)) ⊙ (σ ⊙ τ) = (Ren.to (λ x => x + 1)) ⊙ σ ⊙ τ := by
      funext; case _ x =>
        unfold Subst.compose; simp
        cases τ x <;> simp at *
        rw [lem7]; unfold Subst.compose; simp
    have lem10 (σ τ : Subst $Ty) : ^σ ⊙ ^τ = ^(σ ⊙ τ) := by
      funext; case _ x =>
      cases x
      case _ => unfold Subst.compose; unfold Subst.lift; simp
      case _ n =>
        have lem : ((^σ ⊙ ^τ) ⊙ (Ren.to (λ x => x + 1))) n
          = (^(σ ⊙ τ) ⊙ (Ren.to (λ x => x + 1))) n
        := by rw [lem1, lem4, lem1, lem8, lem1, lem9]
        unfold Subst.compose at lem; unfold Ren.to at lem
        unfold Subst.compose
        simp at lem; simp [*]
    induction $s generalizing $τ $σ
    all_goals (simp at *; try simp [*])
    all_goals (
      unfold Subst.compose; simp
      unfold Subst.apply; simp; split <;> simp [*]
    )
  })

end Subst

import SystemFD.Substitution

inductive Const : Type where
| pointed | unpointed
deriving Repr

inductive Term : Type where
| nil : Term
| cons : Term -> Term -> Term
| kind : Term
| var : Nat -> Term
| const : Const -> Term
| arrowk : Term -> Term -> Term
| all : Term -> Term -> Term
| arrow : Term -> Term -> Term
| appk : Term -> Term -> Term
| appt : Term -> Term -> Term
| app : Term -> Term -> Term
| lamt : Term -> Term -> Term
| lam : Term -> Term -> Term
| cast : Term -> Term -> Term
| case : Term -> Term -> Term
| branch : Term -> Nat -> Term -> Term
| guard : Term -> Nat -> Term -> Term -> Term
| refl : Term -> Term
| sym : Term -> Term
| seq : Term -> Term -> Term
| appc : Term -> Term -> Term
| fst : Term -> Term
| snd : Term -> Term
| allc : Term -> Term -> Term
| apptc : Term -> Term -> Term
| arrowc : Term -> Term -> Term
| eq : Term -> Term -> Term
| letopentype : Term -> Term -> Term
| letopen : Term -> Term -> Term
| letdata : Term -> Nat -> Term -> Term
| letctor : Term -> Term -> Term
| letterm : Term -> Term -> Term -> Term
| insttype : Term -> Term -> Term
| inst : Nat -> Term -> Term -> Term

deriving Repr

notation "★" => Term.const Const.pointed
notation "◯" => Term.const Const.unpointed
infixr:14 " -k> " => Term.arrowk
infixr:14 " -t> " => Term.arrow
infixr:14 " -c> " => Term.arrowc
notation:14 "∀[" A "]" B:14 => Term.all A B
infixl:15 " `@k " => Term.appk
infixl:15 " `@t " => Term.appt
infixl:15 " `@ " => Term.app
notation "Λ[" A "]" t:50 => Term.lamt A t
notation "`λ[" A "]" t:50 => Term.lam A t
infixl:15 " ▹ " => Term.cast
prefix:max "#" => Term.var
notation:14 "∀c[" A "]" B:14 => Term.allc A B
infixl:15 " `; " => Term.seq
infixl:15 " `@c " => Term.appc
notation:15 f:15 " `@c[" a "]" => Term.apptc f a
infixl:15 " ~ " => Term.eq

@[simp]
def rep : Nat -> (A -> A) -> (A -> A)
| 0, _, a => a
| n + 1, f, a => f (rep n f a)

namespace Term
  @[simp]
  def neutral_head : Term -> Option Nat
  | .var x => .some x
  | .app t _ => neutral_head t
  | .appt t _ => neutral_head t
  | .appk t _ => neutral_head t
  | _ => .none

  @[simp]
  def neutral_subst : Term -> Option (Subst Term)
  | .var _ => .some I
  | .app f a => do
    let f' <- neutral_subst f
    .some (.su a :: f')
  | .appt f a => do
    let f' <- neutral_subst f
    .some (.su a :: f')
  | .appk f a => do
    let f' <- neutral_subst f
    .some (.su a :: f')
  | _ => .none

  @[simp]
  def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
  | var x =>
    match f x with
    | .re y => var y
    | .su t => t
  | nil => nil
  | cons hd tl => cons (smap lf f hd) (smap lf f tl)
  | kind => kind
  | const k => const k
  | arrowk t1 t2 => arrowk (smap lf f t1) (smap lf f t2)
  | arrowc t1 t2 => arrowc (smap lf f t1) (smap lf f t2)
  | all t1 t2 => all (smap lf f t1) (smap lf (lf f) t2)
  | arrow t1 t2 => arrow (smap lf f t1) (smap lf f t2)
  | appk t1 t2 => appk (smap lf f t1) (smap lf f t2)
  | appt t1 t2 => appt (smap lf f t1) (smap lf f t2)
  | app t1 t2 => app (smap lf f t1) (smap lf f t2)
  | lamt t1 t2 => lamt (smap lf f t1) (smap lf (lf f) t2)
  | lam t1 t2 => lam (smap lf f t1) (smap lf (lf f) t2)
  | cast t1 t2 => cast (smap lf f t1) (smap lf f t2)
  | case t1 t2 => case (smap lf f t1) (smap lf f t2)
  | branch t1 n t2 => branch (smap lf f t1) n (smap lf (rep n lf f) t2)
  | guard t1 n t2 t3 => guard (smap lf f t1) n (smap lf f t2) (smap lf (rep n lf f) t3)
  | refl t => refl (smap lf f t)
  | sym t => sym (smap lf f t)
  | seq t1 t2 => seq (smap lf f t1) (smap lf f t2)
  | appc t1 t2 => appc (smap lf f t1) (smap lf f t2)
  | fst t => fst (smap lf f t)
  | snd t => snd (smap lf f t)
  | allc t1 t2 => allc (smap lf f t1) (smap lf (lf f) t2)
  | apptc t1 t2 => apptc (smap lf f t1) (smap lf f t2)
  | eq t1 t2 => eq (smap lf f t1) (smap lf f t2)
  | letopentype t1 t2 => letopentype (smap lf f t1) (smap lf (lf f) t2)
  | letopen t1 t2 => letopen (smap lf f t1) (smap lf (lf f) t2)
  | letdata t1 n t2 => letdata (smap lf f t1) n (smap lf (lf f) t2)
  | letctor t1 t2 => letctor (smap lf f t1) (smap lf (lf f) t2)
  | letterm t1 t2 t3 => letterm (smap lf f t1) (smap lf f t2) (smap lf (lf f) t3)
  | insttype t1 t2 => insttype (smap lf f t1) (smap lf (lf f) t2)
  | inst n t1 t2 => inst n (smap lf f t1) (smap lf (lf f) t2)

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
  theorem subst_nil : [σ]nil = nil := by unfold Subst.apply; simp

  @[simp]
  theorem subst_cons : [σ]cons hd tl = cons ([σ]hd) ([σ]tl) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_kind : [σ]kind = kind := by unfold Subst.apply; simp

  @[simp]
  theorem subst_const : [σ]const k = const k := by unfold Subst.apply; simp

  @[simp]
  theorem subst_allk : [σ]arrowk t1 t2 = arrowk ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_all : [σ]all t1 t2 = all ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_arrow : [σ]arrow t1 t2 = arrow ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

 @[simp]
  theorem subst_arrowc : [σ]arrowc t1 t2 = arrowc ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_appk : [σ]appk t1 t2 = appk ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_appt : [σ]appt t1 t2 = appt ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_app : [σ]app t1 t2 = app ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_lamt : [σ]lamt t1 t2 = lamt ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_lam : [σ]lam t1 t2 = lam ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_cast : [σ]cast t1 t2 = cast ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_case : [σ]case t1 t2 = case ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_branch : [σ]branch t1 n t2 = branch ([σ]t1) n ([rep n Subst.lift σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_guard : [σ]guard t1 n t2 t3 = guard ([σ]t1) n ([σ]t2) ([rep n Subst.lift σ]t3) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_refl : [σ]refl t = refl ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_sym : [σ]sym t = sym ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_seq : [σ]seq t1 t2 = seq ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_appc : [σ]appc t1 t2 = appc ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_fst : [σ]fst t = fst ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_snd : [σ]snd t = snd ([σ]t) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_allc : [σ]allc t1 t2 = allc ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_apptc : [σ]apptc t1 t2 = apptc ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_eq : [σ]eq t1 t2 = eq ([σ]t1) ([σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letopentype : [σ]letopentype t1 t2 = letopentype ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letopen : [σ]letopen t1 t2 = letopen ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letdata: [σ]letdata t1 n t2 = letdata ([σ]t1) n ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_letctor: [σ]letctor t1 t2 = letctor ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

 @[simp]
  theorem subst_letterm: [σ]letterm t1 t2 t3 = letterm ([σ]t1) ([σ]t2) ([^σ]t3) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_insttype : [σ]insttype t1 t2 = insttype ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  @[simp]
  theorem subst_inst : [σ]inst n t1 t2 = inst n ([σ]t1) ([^σ]t2) := by unfold Subst.apply; simp

  theorem apply_id {t : Term} : [I]t = t := by
  have lem1 : ^I = @I Term := by
    funext; case _ x =>
    cases x; all_goals (unfold Subst.lift; unfold I; simp)
  have lem2 : ∀ n, rep n Subst.lift I = @I Term := by sorry
  induction t
  all_goals (simp at * <;> try simp [*])

  theorem apply_stable {r : Ren} {σ : Subst Term}
    : r.to = σ -> Ren.apply r = Subst.apply σ
  := by sorry
  -- intro h; funext; case _ x =>
  --   unfold Ren.apply; simp at *
  --   unfold Ren.to; simp
  --   induction x generalizing r σ <;> simp at *
  --   case _ x => rw [<-h]; unfold Ren.to; simp
  --   case _ => simp [*]
  --   case _ =>
  --     simp [*]; rw [Subst.lift_lemma, <-h]
  --     unfold Ren.fro; simp

  theorem apply_compose {s : Term} {σ τ : Subst Term} : [τ][σ]s = [τ ⊙ σ]s := by sorry
  -- solve_compose Term, apply_stable, s, σ, τ


end Term

instance substTypeLaws_Term : SubstitutionTypeLaws Term where
  apply_id := Term.apply_id
  apply_compose := Term.apply_compose
  apply_stable := Term.apply_stable

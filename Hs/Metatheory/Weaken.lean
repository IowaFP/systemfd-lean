import Hs.HsTerm
import Hs.HsJudgment
import SystemFD.Ctx
import Hs.Metatheory.TypeMatch

theorem hs_rename_lift r (A : Frame HsTerm) :
  (∀ x, (Γ d@ x).apply r.to = Δ d@ (r x)) ->
  ∀ x, ((A::Γ) d@ x).apply r.lift.to = (A.apply r.to::Δ) d@ (Ren.lift r x)
:= by
intro h x; simp
cases x <;> simp at *
case _ =>
  rw [Subst.lift_lemma]; simp
  unfold Ren.lift; simp
  rw [Frame.apply_compose, Frame.apply_compose]; simp
case _ x =>
  rw [Subst.lift_lemma]; simp
  unfold Ren.lift; simp
  rw [<-h x, Frame.apply_compose, Frame.apply_compose]; simp

@[simp]
abbrev hs_idx_ren (r : Ren) : HsJudgmentArgs v -> HsJudgmentArgs v :=
  match v with
  | .term => λ (t, A) => ([r.to]t, [r.to]A)
  | .kind => λ (t, A) => ([r.to]t, [r.to]A)
  | .type => λ (t, A) => ([r.to]t, [r.to]A)
  | .ctx => λ () => ()

def hs_rename (r : Ren) : (v : HsVariant) -> {idx : HsJudgmentArgs v} ->
  HsJudgment v Γ1 Γ2 idx ->
  ⊢s[ Δ1 ◆ Δ2 ] ->
  (∀ x, (Γ1 d@ x).apply r.to = Δ1 d@ (r x)) ->
  (∀ x, (Γ2 d@ x).apply r.to = Δ2 d@ (r x)) ->
  HsJudgment v Δ1 Δ2 (hs_idx_ren r idx)
| .kind, (t, τ) , j, wf, f1, f2 => match j with
  | .ax wf' => .ax wf
  | .arrowk h1 h2 => .arrowk (hs_rename r .kind h1 wf f1 f2) (hs_rename r .kind h2 wf f1 f2)
| .type, (t, τ) , j, wf, f1, f2 => match j with
  | @HsJudgment.varTy Γ1 Γ2 x t wf' test gt h => by
    have lem1 : ((Δ1 d@r x).is_datatype || (Δ1 d@r x).is_kind) := by
         rw[<-f1]; simp;
         generalize fh : Γ1 d@ x = f at *;
         cases f;
         all_goals (unfold Frame.is_datatype at test; unfold Frame.is_kind at test; simp at test)
         all_goals (unfold Frame.apply; unfold Frame.get_type at gt; simp at gt; cases gt)
         case _ => unfold Frame.is_kind; simp;
         case _ => unfold Frame.is_datatype; simp
    have lem2 : some ([r.to]t) = (Δ1 d@r x).get_type := by
         rw [<-f1];
         unfold Frame.get_type;
         generalize fh : Γ1 d@ x = f at *;
         cases f;
         all_goals (unfold Frame.is_datatype at test; unfold Frame.is_kind at test; simp at test)
         all_goals (unfold Frame.apply; unfold Frame.get_type at gt; simp at gt; cases gt; simp)
    apply HsJudgment.varTy
    apply wf
    apply lem1
    apply lem2
    apply (hs_rename r .kind h wf f1 f2)
  | .appk h1 h2 h3 h4 => .appk
    (hs_rename r .type h1 wf f1 f2)
    (hs_rename r .type h2 wf f1 f2)
    (hs_rename r .kind h3 wf f1 f2)
    (hs_rename r .kind h4 wf f1 f2)
  | @HsJudgment.allt Γ1 Γ2 A B h1 h2 => by sorry
      -- .allt
      -- (hs_rename r .kind h1 wf f1 f2)
      -- (by have wf' : ⊢s (.kind ([r.to] A) :: Δ) := by
      --      constructor;
      --      case _ =>
      --        match A with
      --        | `★ => simp; apply HsJudgment.ax wf
      --        | k1 `-k> k2 =>
      --          simp; cases h1; case _ j1 j2 =>
      --          apply HsJudgment.arrowk; (apply hs_rename r .kind j1 wf f1 f2); (apply hs_rename r .kind j2 wf f1 f2)
      --      apply wf
      --     have f' := hs_rename_lift r (Frame.kind A) f
      --     have h := @hs_rename (.kind A :: Γ) (.kind ([r.to] A) :: Δ) (Ren.lift r) .type (B, `★) h2 wf' f';
      --     simp at h; unfold Subst.apply at h; rw[Subst.lift_lemma] at h;
      --     apply h)
  | @HsJudgment.arrow Γ1 Γ2 A B h1 h2 => sorry
    -- .arrow
    -- (hs_rename r .type h1 wf f1 f2)
    -- (by have wf' : ⊢s (.empty :: Δ) := by apply HsJudgment.wfempty wf
    --     have f' := hs_rename_lift r (.empty) f
    --     have h := @hs_rename (.empty :: Γ) (.empty :: Δ) (Ren.lift r) .type (B, `★) h2 wf' f';
    --     simp at h; unfold Subst.apply at h; rw[Subst.lift_lemma] at h; apply h)
  | @HsJudgment.farrow Γ1 Γ2 A B h1 h2 h3  => sorry
  -- .farrow
  --   (hs_rename r .type h1 wf f1 f2)
  --   (by apply hs_valid_head_variable_subst Γ.is_opent Δ.is_opent _ h2
  --       intro n h;
  --       have f' := f n; unfold Frame.apply at f'; simp at f'
  --       have h' := opent_indexing_exists h
  --       cases h'; case _ w h' =>
  --       rw [h'] at f'; simp at f'; unfold Ren.to; simp; rw[<-f']; unfold Frame.is_opent; simp)
  --   (by have wf' : ⊢s (.empty :: Δ) := by apply HsJudgment.wfempty wf
  --       have f' := hs_rename_lift r (.empty) f
  --       have h := @hs_rename (.empty :: Γ) (.empty :: Δ) (Ren.lift r) .type (B, `★) h3 wf' f';
  --       simp at h; unfold Subst.apply at h; rw[Subst.lift_lemma] at h; apply h)
| .term, (t, τ) , j, wf, f1, f2 => match j with
  | @HsJudgment.implicitAllI Γ A t τ h1 h2 h3 => by
    simp
    have w1 : (Δ1 ;; Δ2 ⊢κ ([r.to] A) : `□) := by
         simp; sorry
         -- apply (hs_rename r .kind h2 wf _ f2)
    have wf' : ⊢s[(.kind ([r.to] A) :: Δ1) ◆ (.kind ([r.to] A) :: Δ2) ] := by
       apply HsJudgment.wfkind;
       sorry
       sorry
       -- apply hs_rename r .kind h2 wf f1 f2
       -- apply wf
    have f1' := hs_rename_lift r (.kind A) f1
    have f2' := hs_rename_lift r (.kind A) f2
    -- have lem1 := @hs_rename (.kind A :: Γ) (.kind ([r.to]A) :: Δ) (Ren.lift r) .term (t, τ) h1 wf' f1' f2'; simp at lem1
    -- have lem2 := hs_rename r .kind h2 wf f1 f2; simp at lem2
    -- apply HsJudgment.implicitAllI
    -- sorry
    -- sorry
    sorry -- apply lem2
  | @HsJudgment.implicitArrI Γ1 Γ2 π τ t h1 h2 h3 h4 h5 => by sorry
  --   have lem1 := hs_rename r .type h1 wf f1 f2; simp at lem1
  --   have wf' : ⊢s (.empty :: Δ) := by
  --      apply HsJudgment.wfempty;
  --      apply wf
  --   have f' := hs_rename_lift r (.empty) f
  --   have lem2 := @hs_rename (.empty :: Γ) (.empty :: Δ) (Ren.lift r) .type (τ, `★) h2 wf' f'; simp at lem2
  --   have lem3 : HsValidHeadVariable ([r.to]π) Δ.is_opent := by
  --     apply hs_valid_head_variable_subst _ _ _;
  --     case _ => apply h3
  --     case _ =>
  --        intro n test; have f' := f n;
  --        unfold Ren.to; simp; rw[<-f'];
  --        unfold Frame.is_opent; unfold Ctx.is_opent at test;
  --        replace test := opent_indexing_exists test;
  --        cases test; case _ test =>
  --        rw[test]; unfold Frame.apply; simp
  --   have wf' : ⊢s (.type ([r.to]π) :: Δ) := by
  --      apply HsJudgment.wftype;
  --      apply hs_rename r .type h1 wf f1 f2
  --      apply wf
  --   have f' := hs_rename_lift r (.type π) f
  --   have lem4 := @hs_rename (.type π :: Γ) (.type ([r.to] π) :: Δ) (Ren.lift r) .term (t, τ) h4 wf' f';
  --   simp at lem4
  --   apply HsJudgment.implicitArrI
  --   apply lem1
  --   unfold Subst.apply at lem2; rw[Subst.lift_lemma] at lem2; apply lem2
  --   apply lem3
  --   unfold Subst.apply at lem4; rw[Subst.lift_lemma] at lem4; sorry
  | @HsJudgment.implicitAllE Γ1 Γ2 A τ t e τ' h1 h2 h3 h4 h5 =>  by sorry
  -- .implicitAllE
  --    (hs_rename r .type h1 wf f1 f2)
  --    (hs_rename r .kind h2 wf f1 f2)
  --    (hs_rename r .term h3 wf f1 f2)
  --    (hs_rename r .type h4 wf f1 f2)
  --    (by have lem1 : [.su ([r.to]e)::I]([^r.to]τ) = [.su ([r.to]e)::I]HsTerm.smap Subst.lift (^r.to) τ := by rfl
  --        have lem : [r.to][.su e::I]τ = [.su ([r.to]e)::I]([^r.to] τ) := by simp
  --        rw[<-lem1]; rw[<-lem]; congr)
  | @HsJudgment.implicitArrE Γ1 Γ2 t π τ e τ' h1 h2 h3 h4 => by sorry
  --    simp
  --    have lem1 := hs_rename r .term h1 wf f1 f2; simp at lem1
  --    have lem2 := hs_rename r .term h2 wf f1 f2; simp at lem2
  --    have lem3 : [r.to][.su e::I]τ = [.su ([r.to]e)::I][.re 0::S ⊙ r.to]τ := by simp
  --    have lem4 := hs_rename r .type h4 wf f1 f2; simp at lem4
  --    apply HsJudgment.implicitArrE;
  --    apply lem1
  --    apply lem2
  --    rw[<-lem3]; congr
  --    apply lem4

  | @HsJudgment.var Γ x T wf' test gt => by sorry
    -- .var wf
    -- (by rw[<-f]; simp;
    --     generalize hf : Γ d@ x = f at *;
    --     cases f;
    --     all_goals (unfold Frame.is_ctor at test; unfold Frame.is_term at test; unfold Frame.is_type at test;
    --                simp at test)
    --     all_goals (unfold Frame.apply; unfold Frame.get_type at gt; simp at gt; cases gt)
    --     case _ => unfold Frame.is_type; simp
    --     case _ => unfold Frame.is_ctor; simp
    --     case _ => unfold Frame.is_term; simp)
    -- (by rw [<-f];
    --     unfold Frame.get_type;
    --     generalize fh : Γ d@ x = f at *;
    --     cases f;
    --     all_goals (unfold Frame.is_ctor at test; unfold Frame.is_term at test; unfold Frame.is_type at test;
    --                simp at test)
    --     all_goals (unfold Frame.apply; unfold Frame.get_type at gt; simp at gt; cases gt; simp))
  | @HsJudgment.lam Γ A t B h1 h2 h3 => by sorry
    -- .lam
    --  (hs_rename r .type h1 wf f1 f2)
    --  (by have wf' : ⊢s (.type ([r.to] A) :: Δ) := by
    --           apply HsJudgment.wftype;
    --           apply hs_rename r .type h1 wf f1 f2
    --           apply wf
    --      have f' := hs_rename_lift r (Frame.type A) f
    --      have h := @hs_rename (.type A :: Γ) (.type ([r.to]A) :: Δ) (Ren.lift r) .term (t, B) h2 wf' f';
    --      simp at h; unfold Subst.apply at h; rw[Subst.lift_lemma] at h; apply h)
    --  (by have wf' : ⊢s (.empty :: Δ) := by apply HsJudgment.wfempty wf
    --      have f' := hs_rename_lift r (.empty) f
    --      have h := @hs_rename (.empty :: Γ) (.empty :: Δ) (Ren.lift r) .type (B, `★) h3 wf' f';
    --      simp at h; unfold Subst.apply at h; rw[Subst.lift_lemma] at h; apply h)
  | @HsJudgment.app Γ t1 A B t2 B' h1 h2 h3 h4 h5 => by sorry
    -- .app
    --   (hs_rename r .term h1 wf f1 f2)
    --   (hs_rename r .term h2 wf f1 f2)
    --   (by have lem1 : [.su ([r.to]t2)::I]([^r.to]B) = [.su (HsTerm.smap Subst.lift r.to t2)::I]HsTerm.smap Subst.lift (^r.to) B := by rfl
    --       have lem : [r.to][.su t2::I]B = [.su ([r.to]t2)::I]([^r.to] B) := by simp
    --       rw[<-lem1]; rw[<-lem]; congr)
    --   (hs_rename r .type h4 wf f1 f2)
    --   (hs_rename r .type h5 wf f1 f2)
  | @HsJudgment.hslet Γ A t1 B' B t2 h1 h2 h3 h4 h5 => by sorry
     -- apply HsJudgment.hslet;
     -- apply (hs_rename r .type h1 wf f1 f2)
     -- apply (hs_rename r .term h2 wf f1 f2)
     -- rfl
     -- case _ =>
     --   have wf' : ⊢s (.term ([r.to] A) ([r.to] t1) :: Δ) := by
     --          apply HsJudgment.wfterm;
     --          apply hs_rename r .type h1 wf f1 f2
     --          apply hs_rename r .term h2 wf f1 f2
     --          apply wf
     --   have f' := hs_rename_lift r (Frame.term A t1) f
     --   have h := @hs_rename (.term A t1 :: Γ) (.term ([r.to]A) ([r.to] t1) :: Δ) (Ren.lift r) .term (t2, B') h4 wf' f';
     --   have lem : [S][r.to]B = [r.lift.to][S]B := by
     --        rw[Subst.apply_compose_commute]; rw[Subst.lift_lemma]; simp
     --   simp at h; rw [h3] at h; rw[lem];
     --   unfold Subst.apply at h; rw[Subst.lift_lemma] at h; unfold Subst.apply;
     --   rw[Subst.lift_lemma]; apply h
     -- apply (hs_rename r .type h5 wf f1 f2)

  | .hsIte h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    .hsIte
      (hs_rename r .type h1 wf f1 f2) (hs_rename r .type h2 wf f1 f2)
      (hs_rename r .type h3 wf f1 f2) (hs_rename r .type h4 wf f1 f2)
      (hs_rename r .term h5 wf f1 f2) (hs_rename r .term h6 wf f1 f2)
      (hs_rename r .term h7 wf f1 f2) (hs_rename r .term h8 wf f1 f2)
      (by apply hs_stable_type_match_subst
          case _ =>
            intro n1 n2 j; unfold Ren.to at j; simp at j;
            have f' := f1 n1; rw[j] at f'; apply f'
          case _ => intro n test; unfold Ren.to; simp
          apply h9
      )
      (by apply hs_prefix_type_match_subst _ _;
          case _ => apply h10
          case _ =>
            intro n1 n2 j; unfold Ren.to at j; simp at j;
            have f' := f1 n1; rw[j] at f'; apply f'
          case _ => intro n test; unfold Ren.to; simp
      )
      (by apply hs_valid_head_variable_subst _ _ _;
          case _ => apply h11
          case _ =>
               intro n test; have f' := f1 n;
               unfold Ren.to; simp; rw[<-f'];
               unfold Frame.is_datatype; unfold Ctx.is_datatype at test;
               replace test := datatype_indexing_exists test;
               cases test; case _ test =>
               rw[test]; unfold Frame.apply; simp)
      (by apply hs_valid_head_variable_subst _ _ _;
          case _ => apply h12
          case _ =>
               intro n test; have f' := f1 n;
               unfold Ren.to; simp; rw[<-f'];
               unfold Frame.is_ctor; unfold Ctx.is_ctor at test;
               replace test := ctor_indexing_exists test;
               cases test; case _ test =>
               rw[test]; unfold Frame.apply; simp)

| .ctx, () , j, wf, f1, f2 => by simp; apply wf
termination_by v idx h => h.size

@[simp]
def hs_weaken_type :
  ⊢s[ (f :: Γ) ◆ (f :: Γ) ]->
  Γ ;; Γ ⊢τ t : A ->
  (f::Γ) ;; (f::Γ) ⊢τ ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .type h wf (by intro; rw [Subst.to_S]; simp) (by intro; rw [Subst.to_S]; simp)


@[simp]
def hs_weaken_kind :
  ⊢s[ (f :: Γ) ◆ (f :: Γ) ]->
  Γ ;; Γ ⊢κ t : A ->
  (f::Γ) ;; (f::Γ) ⊢κ ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .kind h wf (by intro; rw [Subst.to_S]; simp) (by intro; rw [Subst.to_S]; simp)

@[simp]
def hs_weaken_kind_unique :
  ⊢s[ (f :: Γ) ◆ (f :: Γ) ]->
  Γ ;; Γ ⊢κ t : A ->
  (f::Γ) ;; (f::Γ) ⊢κ t : A
| wf , HsJudgment.ax wf' => HsJudgment.ax wf
| wf , .arrowk h1 h2 => HsJudgment.arrowk (hs_weaken_kind_unique wf h1) (hs_weaken_kind_unique wf h2)

@[simp]
def hs_weaken_term :
  ⊢s[ (f :: Γ) ◆ (f :: Γ) ]->
  Γ ;; Γ ⊢t t : A ->
  (f::Γ) ;; (f::Γ) ⊢t ([S]t) : ([S]A)
| wf , h => hs_rename (λ x => x + 1) .term h wf (by intro; rw [Subst.to_S]; simp) (by intro; rw [Subst.to_S]; simp)

@[simp]
def hs_weaken_empty_term :
  Γ ;; Γ ⊢t t : A ->
  (.empty::Γ) ;; (.empty::Γ) ⊢t ([S]t) : ([S]A)
 := λ x => hs_weaken_term (.wfempty (hs_judgment_ctx_wf .term x)) x

@[simp]
def hs_weaken_empty_type :
  Γ ;; Γ ⊢τ t : A ->
  (.empty::Γ) ;; (.empty::Γ) ⊢τ ([S]t) : ([S]A)
 := λ x => hs_weaken_type (.wfempty (hs_judgment_ctx_wf .type x)) x

@[simp]
def hs_weaken_empty_kind :
  Γ ;; Γ ⊢κ t : A ->
  (.empty::Γ) ;; (.empty::Γ) ⊢κ ([S]t) : ([S]A)
 := λ x => hs_weaken_kind (.wfempty (hs_judgment_ctx_wf .kind x)) x

@[simp]
def hs_weaken_type_term :
  Γ ;; Γ ⊢τ T : `★ ->
  Γ ;; Γ ⊢t t : A ->
  (.type T::Γ) ;; (.type T::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken_term (.wftype h1 (hs_judgment_ctx_wf .type h1)) h2

@[simp]
def hs_weaken_kind_term :
  Γ ;; Γ ⊢κ T : `□ ->
  Γ ;; Γ ⊢t t : A ->
  (.kind T::Γ) ;; (.kind T::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken_term (.wfkind h1 (hs_judgment_ctx_wf .kind h1)) h2

@[simp]
def hs_weaken_kind_type :
  Γ ;; Γ ⊢κ T : `□ ->
  Γ ;; Γ ⊢τ t : A ->
  (.kind T::Γ) ;; (.kind T::Γ) ⊢τ ([S]t) : ([S]A)
:= λ h1 h2 => hs_weaken_type (.wfkind h1 (hs_judgment_ctx_wf .kind h1)) h2

-- theorem weaken_kind :
--   Γ ⊢s T : `□ ->
--   Γ ⊢s t : A ->
--   (.kind T::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_datatype_term :
  Γ ;; Γ ⊢κ T : `□ ->
  Γ ;; Γ ⊢t t : A ->
  (.datatype T::Γ) ;; (.datatype T::Γ) ⊢t ([S]t) : ([S]A)
:= sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_ctor :
  Γ ;; Γ ⊢τ T : `★ ->
  ValidHsCtorType Γ T ->
  Γ ;; Γ ⊢t t : A ->
  (.ctor T::Γ) ;; (.ctor T::Γ) ⊢t ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_opent :
  Γ ;; Γ ⊢κ T : `□ ->
  Γ ;; Γ ⊢t t : A ->
  (.opent T::Γ) ;; (.opent T::Γ) ⊢κ ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

-- def hs_weaken_openm :
--   Γ ⊢s T : `★ ->
--   Γ ⊢s t : A ->
--   (.openm T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- by
-- intro j1 j2; apply hs_rename _ j2
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1
-- case _ => intro x; simp; rw [Subst.to_S]

-- def hs_weaken_insttype :
--   Γ ⊢s T : `★ ->
--   ValidHsInstType Γ T ->
--   Γ ⊢s t : A ->
--   (.insttype T::Γ) ⊢s ([S]t) : ([S]A) := sorry
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply hs_judgment_ctx_wf j1; apply j2
-- case _ => intro x; simp; rw [Subst.to_S]

-- theorem weaken_inst :
--   .openm T = Γ d@ x ->
--   Γ ⊢s b : T ->
--   Γ ⊢s t : A ->
--   (.inst #x b::Γ) ⊢s ([S]t) : ([S]A)
-- := by
-- intro j1 j2 j3; apply hs_rename _ j3
-- case _ => constructor; apply j1; apply j2; apply hs_judgment_ctx_wf j2
-- case _ => intro x; simp; rw [Subst.to_S]

def hs_weaken_term_term :
  Γ ;; Γ ⊢τ T : `★ ->
  Γ ;; Γ ⊢t b : T ->
  Γ ;; Γ ⊢t t : A ->
  (.term T b::Γ) ;; (.term T b::Γ) ⊢t ([S]t) : ([S]A)
:= λ h1 h2 h3 => hs_weaken_term (.wfterm h1 h2 (hs_judgment_ctx_wf .type h1)) h3

def hs_weaken_term_type :
  Γ ;; Γ ⊢τ T : `★ ->
  Γ ;; Γ ⊢t b : T ->
  Γ ;; Γ ⊢τ t : A ->
  (.term T b::Γ) ;; (.term T b::Γ) ⊢τ ([S]t) : ([S]A)
:= λ h1 h2 h3 => hs_weaken_type (.wfterm h1 h2 (hs_judgment_ctx_wf .type h1)) h3



def hs_replace_empty_kind :
  Γ ;; Γ ⊢τ A : `★ ->
  (.empty :: Γ) ;; (.empty :: Γ) ⊢κ B : `□ ->
  (.type A :: Γ) ;; (.type A :: Γ) ⊢κ B : `□
| ja, .ax h => by apply HsJudgment.ax; cases h; case _ h => apply HsJudgment.wftype; assumption; assumption
| ja, .arrowk h1 h2 => by apply HsJudgment.arrowk (hs_replace_empty_kind ja h1) (hs_replace_empty_kind ja h2)


def hs_replace_empty_type :
  Γ ;; Γ ⊢τ A : `★ ->
  (.empty :: Γ) ;; (.empty :: Γ) ⊢τ B : `★ ->
  (.type A :: Γ) ;; (.type A :: Γ) ⊢τ B : `★
| ja, .allt h1 h2 => by apply HsJudgment.allt; apply hs_replace_empty_kind ja h1; sorry
| ja, .varTy h1 h2 h3 h4 => by sorry
| ja, .arrow h1 h2 => by sorry
| ja, .farrow h1 h2 h3 => by sorry
| ja, .appk h1 h2 h3 h4  => by sorry

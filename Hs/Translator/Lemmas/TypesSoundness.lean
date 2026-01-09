import Hs.HsTerm
import Hs.Monad
import Hs.Translator.Lemmas.KindSoundness
import Hs.Translator.Lemmas.Utils

import Hs.Translator.HsTerm
import Hs.SynthInstance

import SystemFD.Term
import SystemFD.Metatheory.Inversion

import Batteries.Lean.Except

import Mathlib.Data.Prod.Basic

set_option maxHeartbeats 10000000


theorem is_type_list_reverse (τs : List Term) :
  (∀ τ ∈ τs, Term.IsType τ) -> ∀ τ ∈ τs.reverse, Term.IsType τ := by
  intro h t h2
  have lem : t ∈ τs := by simp at h2; assumption
  replace h := h t lem
  assumption

theorem hs_is_type_list_reverse (τs : List HsTerm) :
  (∀ τ ∈ τs, HsTerm.IsType τ) -> ∀ τ ∈ τs.reverse, HsTerm.IsType τ := by
  intro h t h2
  have lem : t ∈ τs := by simp at h2; assumption
  replace h := h t lem
  assumption


theorem hs_is_type_spine_application' (τh : HsTerm) (τs : List HsTerm) :
  τh.IsType ->
  (∀ τ ∈ τs, HsTerm.IsType τ) ->
  HsTerm.IsType (τh.mk_kind_apps' τs) := by
intro h1 h2; simp at *
induction τs using List.foldr.induct <;> simp at *
case _ => assumption
case _ ih =>
  cases h2; case _ h2a h2b =>
  constructor;
  replace ih := ih h2b; assumption
  assumption


theorem hs_is_type_spine_application (τh : HsTerm) (τs : List HsTerm) :
  τh.IsType ->
  (∀ τ ∈ τs, HsTerm.IsType τ) ->
  HsTerm.IsType (τh.mk_kind_apps τs) := by
intro h1 h2
have lem := hs_is_type_list_reverse τs h2
unfold HsTerm.mk_kind_apps
apply hs_is_type_spine_application'
assumption
assumption


theorem is_type_spine_application' (τh : Term) (τs : List Term) :
  τh.IsType ->
  (∀ τ ∈ τs, Term.IsType τ) ->
  Term.IsType (τh.mk_kind_apps' τs) := by
intro h1 h2; simp at *
induction τs using List.foldr.induct <;> simp at *
case _ => assumption
case _ ih =>
  cases h2; case _ h2a h2b =>
  constructor;
  replace ih := ih h2b; assumption
  assumption


theorem typing_spine_application {Γ : Ctx Term} {h : Term} {τs : List Term} {k : Term}:
  Γ ⊢ k : □ ->
  Γ ⊢ h : k ->
  k.split_kind_arrow = .some (κs, ret_κ) ->
  κs.length = τs.length ->
  let ls := κs.attach.zip τs.attach
  (∀ (i : Nat) (p : i < ls.length), Γ ⊢ (ls[i].2.val) : (ls[i].1.val)) ->
  Γ ⊢ (h.mk_kind_apps τs) : ret_κ := by
intro j1 j2 h1 h2 ls j3;
have wf := judgment_ctx_wf j1
have lem := kinding_split_arrow wf j1 h1
induction τs using List.foldr.induct generalizing h k κs <;> simp at *
case _ =>
  cases h2;

  simp at ls; cases ls;
  case _ =>
    rw[Option.bind_eq_some_iff] at h1; cases h1; case _ w h1 =>
    cases h1; case _ h1 e =>
    simp at e; cases e; case _ e1 e2 =>
    have e := @Prod.mk.eta (List Term) Term w
    rw[<-e] at h1
    cases e2;
    rw[e1] at h1;
    have lem1 := @kind_split_empty_κs k w.snd h1
    subst lem1
    assumption
  case _ h _ => exfalso; apply h.1.property

case _ τ τs ih =>
  cases lem;
  case _ lem1 lem2 =>
  have lem3 := list_non_empty h2
  cases lem3; case _ κ' lem3 =>
  cases lem3; case _ κs' lem3 =>
  cases lem3
  simp at h2;

  have ih' := @ih κs' (h `@k τ) (Term.mk_kind_arrow ret_κ κs')
  apply ih'
  case _ =>
    apply kinding_mk_kind_arrow wf;
    intro k h;
      apply lem2 k; simp_all
    assumption
  case _ =>
    rw[Option.bind_eq_some_iff] at h1; cases h1; case _ w h1 =>
    cases h1; case _ w1 h1 =>
    injection h1; case _ h1 =>
    injection h1; case _ h1a h1b =>
    rw[<-@Prod.mk.eta (List Term) Term w] at w1
    simp at h1a;
    constructor;
    sorry
    sorry
    apply w.1.head; rw[h1a]; simp

  sorry
  assumption
  case _ =>
    intro i p
    have j3' := j3 i
    sorry
  assumption
  intro k h
  apply lem2 k
  simp; simp_all
 -- have lem1 : ∃ κshd κstl, κs = (.cons κshd κstl) := by
 --   sorry
 -- have lem2 : ∃ τshd τstl, τs = (.cons τshd τstl) := by
 --   sorry
 -- cases lem1; case _ κshd lem1 =>
 -- cases lem1; case _ κstl lem1 =>
 -- cases lem2; case _ τshd lem2 =>
 -- cases lem2; case _ τstl lem2 =>
 -- cases lem1; cases lem2
 -- unfold Term.split_kind_arrow_aux at h1;
 -- split at h1 <;> try simp at h1
 -- case _ =>
 --    simp at h2



theorem is_type_spine_application (τh : Term) (τs : List Term) :
  τh.IsType ->
  (∀ τ ∈ τs, Term.IsType τ) ->
  Term.IsType (τh.mk_kind_apps τs) := by
intro h1 h2
have lem := is_type_list_reverse τs h2
unfold Term.mk_kind_apps
apply is_type_spine_application'
assumption
assumption

theorem compile_type_shape_soundness (Γ : Ctx Term) (k : Term) (τ : HsTerm) (τ' : Term): ⊢ Γ ->
 HsTerm.IsType τ ->
 Term.IsKind k ->
 compile_type Γ k τ = .ok τ' ->
 Term.IsType τ' := by
sorry
-- intro wf j1 j2 j3
-- induction Γ, k, τ using compile_type.induct generalizing τ' <;> simp at *

-- all_goals try (
-- case _ ih1 ih2 =>
--   cases j3; case _ j3 =>
--   cases j3; case _ j3 =>
--   cases j3; cases j1; case _ h1 _ h2 h3 h4 =>
--   cases h2; case _ A' B' h2 e =>
--   cases e
--   have ih1' := ih1 A' wf h3 (by constructor) h1
--   replace ih2 := ih2 B' (Judgment.wfempty wf) h4 (by constructor) h2
--   constructor; assumption; assumption)

-- case _ Γ K A ih =>
--   cases j3; case _ j3 =>
--   cases j3; case _ j3 =>
--   cases j3; cases j1; case _ K' h1 A' h2 h3 h4 =>
--   cases h2; case _ h2 e =>
--   cases e
--   have lem' : Except.ok K' = DsM.ok K' := by simp
--   rw[lem'] at h1;

--   have lem := compile_kind_sound wf h3 h1
--   have wf' : ⊢ (.kind K' :: Γ) := by constructor; assumption; assumption
--   replace ih := @ih K' A' wf' h4 (by constructor) h2
--   have lem := kind_shape lem rfl
--   constructor; assumption; assumption

-- case _ tnf _ _ _ => simp_all; rw[tnf] at j3; simp at j3
-- case _ sp idx _ tnfp _ _ _ _ =>
--  split at j3
--  case _ => cases j3
--  case _ =>
--  split at j3
--  /- head is a variable -/
--  case _ =>
--    simp at j3; cases j3; case _ n tnfp idx tnfp' κ j3 =>
--    rw[tnfp] at tnfp'; cases tnfp'
--    case _ tnfp' tnfp'' _ _ _ _ _ =>
--    rw[tnfp] at tnfp'; cases tnfp'; clear tnfp''; cases j3; case _ j4 j3 =>
--    simp at j3; split at j3
--    case _ wfk =>
--      split at j3
--      case _ => simp at j3
--      case _ κs ret_κ h1 =>
--      split at j3
--      case _ j4 =>
--        simp at j4
--        cases j4; case _ j4 j5 =>
--        cases j4; case _ j4 j6 =>
--        have e := Term.eq_of_beq j4; cases e; clear j4
--        rw[Except.bind_eq_ok] at j3; cases j3
--        case _ exp_κ τ _ _ _ ih τs j3 =>
--        cases j3; case _ j3 j7 =>
--        cases j7; rw[List.foldl_eq_foldr_reverse]
--        have lem1 := HsTerm.hs_type_neutral_form_is_type j1 tnfp
--        have lem2 := HsTerm.hs_is_type_neutral_form j1 tnfp -- TODO Use Lem1 here
--        rw[<-List.mapM'_eq_mapM] at j3

--        cases lem1; case _ lem1a =>
--        have κ_wf : κ.IsKind := wf_kind_shape_sound wfk
--        have lem3 := kind_shape_split_arrow κ_wf h1
--        cases lem3; case _ lem3a lem3b =>
--        apply is_type_spine_application
--        case _ => constructor
--        case _ ih _ _ =>
--          intro τ' τ'_in_τs
--          have lem3 := mapM'_elems_image j3 τ' τ'_in_τs
--          cases lem3; case _ lem3 =>
--          cases lem3; case _ w w_in_sp lem3 =>
--          simp at lem3; split at lem3 <;> simp at lem3
--          case _ contra => simp at contra
--          case _ e _ =>
--            have lem2' := lem2 (w.val.snd.val.fst, w.val.snd.val.snd) w.val.snd.property
--            simp at lem2'; cases lem2'
--            apply ih κs w.val.fst w.val.fst.property (w.val.snd.val.fst) _ _ _ τ' wf _ _ lem3
--            apply w.val.snd.property
--            apply w.property
--            assumption
--            apply lem3b w.val.fst.val w.val.fst.property
--          case _ contra => simp at contra

--      case _ => simp at j3
--    case _ => simp at j3

--  /- head is a not a variable, bogus case -/
--  case _ => cases j3
-- case _ tnf _ _ _ _ => simp_all; rw[tnf] at j3; simp at j3;

-- theorem compile_type_sound (k : Term) (τ : HsTerm) :
--   ⊢ Γ ->
--   Term.IsKind k ->
--   HsTerm.IsType τ ->
--   compile_type Γ k τ = .ok τ' ->
--   Γ ⊢ τ' : k := by
-- intro wf j1 j2 j
-- induction Γ, k, τ using compile_type.induct generalizing τ' <;> simp at *
-- case _ A B ih1 ih2 => -- a → b
--   cases j; case _ w1 j =>
--   cases j; case _ h1 j =>
--   cases j; case _ w2 j =>
--   cases j; case _ h2 j =>
--   cases j; cases j2;
--   case _ e1 e2 =>
--   have wf' := Judgment.wfempty wf
--   replace ih1 := @ih1 w1 wf (by constructor) e1 h1
--   replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
--   constructor; assumption; assumption
-- case _ ih1 ih2 => -- a ⇒ b
--   cases j; case _ w1 j =>
--   cases j; case _ h1 j =>
--   cases j; case _ w2 j =>
--   cases j; case _ h2 j =>
--   cases j; cases j2;
--   case _ e1 e2 =>
--   have wf' := Judgment.wfempty wf
--   replace ih1 := @ih1 w1 wf (by constructor) e1 h1
--   replace ih2 := @ih2 w2 wf' (by constructor) e2 h2
--   constructor; assumption; assumption
-- case _ Γ A B ih => -- ∀[a] b
--   cases j; case _ w1 j =>
--   cases j; case _ h1 j =>
--   cases j; case _ w2 j =>
--   cases j; case _ h2 j =>
--   cases j; cases j2;
--   case _ e1 e2 =>
--   have lem1 := compile_kind_sound wf e1 h1
--   have wf' := Judgment.wfkind lem1 wf
--   replace ih := @ih w1 w2 wf' (by constructor) e2 h2
--   constructor; assumption; assumption
-- case _ k τ tnf tnfp _ _ _ =>
--   split at j; cases j
--   case _ e => rw [tnfp] at e; cases e
-- case _ k τ sp h tnfp tnf _ _ _ ih =>
--   split at j; cases j
--   case _ e =>
--   rw[tnf] at e; cases e;
--   clear tnf; clear tnfp;
--   split at j
--   case _ he1 he2 =>
--     cases he1; cases he2;
--     rw[Except.bind_eq_ok] at j;
--     cases j; case _ w1 j =>
--     cases j; case _ t1 j =>
--     simp at j; split at j <;> try simp at j
--     case _ wfk =>
--     split at j <;> try simp at j
--     split at j <;> try simp at j
--     case _ κs ret_κ h1 h2 =>
--     cases j; case _ τs j =>
--     simp at h2; cases h2; case _ h2 h3 =>
--     cases h2; case _ h2 h4 =>
--     have e := Term.eq_of_beq h2; cases e; clear h2
--     cases j; case _ j e =>
--     cases e; rw[<-List.mapM'_eq_mapM] at j; rw[List.foldl_eq_foldr_reverse]
--     have lem1 := kinding_split_arrow wf (wf_kind_sound wfk wf) h1
--     cases lem1; case _ Γ _ _ _ _ _ lem1 lem2 =>
--     have lem3 := mapM'_elems_image j

--     have lem4 : Γ ⊢ #h : w1 := by
--       constructor; assumption
--       case _ =>
--         unfold DsM.toDsM at t1; split at t1 <;> simp at t1
--         cases t1; symm; assumption
--     have lem5 : Γ ⊢ w1 : □ := (wf_kind_sound wfk wf)
--     have lem6 : κs.length = τs.reverse.length := by sorry -- becuase τs sp and κs are of the same length

--     apply typing_spine_application
--     sorry
--     sorry
--     sorry
--     sorry
--     sorry
--     sorry

--     case _ contra => sorry



--     -- lem5 lem4 h1 lem6
--     -- intro e p
--     -- have lem7 := lem3 e.val.snd.val (by sorry)
--     -- cases lem7; case _ w3 lem7 =>
--     -- cases lem7; case _ w4 lem7 =>
--     -- simp at lem7; split at lem7 <;> simp at lem7
--     -- case _ contra => simp at contra
--     -- case _ =>
--     --   apply @ih κs.attach
--     --   case _ => sorry
--     --   assumption
--     --   case _ => sorry
--     --   case _ =>
--     --     sorry
--     --   sorry
--     --   sorry
--     --   sorry
--     --   sorry
--     --   sorry


--   case _ tnf ih =>
--   rw[tnf] at e; cases e;
--   have ih' := ih h e rfl; simp at ih'

-- case _ k τ tnf tnfp _ _ _ =>
--   split at j;
--   · cases j
--   case _ h1 => rw[h1] at tnf; cases tnf; simp at j

@[simp]
abbrev HsNeutralFormWellTypedType (Γ : HsCtx HsTerm) : (i : JIdx) -> Nat -> List (HsSpineVariant × HsTerm) -> JudgmentType i -> Prop
| .CtxJ => λ _ _ _ => true
| .TermJ => λ _ _ _ => true
| .KindJ => λ _ _ _ => true
| .TypeJ => λ h sp (A, _) =>
  A.neutral_form = .some (`#h, sp) ->
  (∃ k, (Γ s@ h) = .kind k ∨ (Γ s@ h) = .tycon k)  ∧
  ∀ e ∈ sp, ∃ k, HsJudgment .TypeJ Γ (e.2, k)

theorem hs_neutral_form_well_typed {Γ : HsCtx HsTerm} {h : Nat} {sp : List (HsSpineVariant × HsTerm)}:
  HsJudgment i Γ jty ->
  HsNeutralFormWellTypedType Γ i h sp jty
  := by
intro j
induction j generalizing h sp <;> simp at *
case _ ih1 ih2 =>
 intro h1;
 rw[Option.bind_eq_some_iff] at h1
 cases h1; case _ w h1 =>
 cases h1; case _ h1a h2a =>
 injection h2a; case _ h2a =>
 injection h2a; case _ e1 e2 =>
 have lem : w = (w.1, w.2) := by simp
 rw[lem] at h1a; rw[e1] at h1a

 replace ih1 := @ih1 h w.2 h1a;
 cases ih1
 constructor
 assumption
 case _ ih =>
 rw[<-e2]
 intro a b ab_in_sp
 replace ih := ih a b
 simp at ab_in_sp
 cases ab_in_sp
 case _ h => replace ih := ih h; assumption
 case _ h =>
   cases h; case _ k _ _ _ _ _ _ _ h1 h2 =>
   cases h1; cases h2; exists k

inductive FrameEquiv (Γ : HsCtx HsTerm) (Γ' : Ctx Term): FrameMetadata HsTerm -> Frame Term -> Prop where
| emptyEquiv : FrameEquiv Γ Γ' .empty .empty
| kindEquiv :
  (compile_kind Γ' □ t = .ok t' ∧ HsJudgment .KindJ Γ (t, `□)) ->
  FrameEquiv Γ Γ' (.kind t) (.kind t')
-- TODO Fix this
| typeEquiv :
  (compile_kind Γ' □ K = .ok K' ∧ HsJudgment .KindJ Γ (t, `□)) ->
  FrameEquiv Γ  Γ' (.type K) (.type K')
| dataconEquiv : FrameEquiv Γ  Γ' (.datacon T) (.ctor T')
| tyconEquiv :
 (compile_kind Γ' □ K = .ok K' ∧ HsJudgment .KindJ Γ (t, `□)) ->
 FrameEquiv Γ  Γ' (.tycon K) (.datatype K')
| clsconEquiv : compile_kind Γ' □ K = .ok K' -> FrameEquiv Γ  Γ' (.clscon K) (.opent K')

@[simp]
abbrev CtxEquiv (Γ : HsCtx HsTerm) (Γ' : Ctx Term) := ∀ i, FrameEquiv Γ Γ' (Γ s@ i) (Γ' d@ i)


-- Does this need renaming and weakening lemmas?
def lift_ctx_equiv (Γ : HsCtx HsTerm) (Γ' : Ctx Term) :
  CtxEquiv Γ Γ' ->
  CtxEquiv (.empty :: Γ ) (.empty :: Γ') := by

sorry

theorem FrameEquivRefineType :
  (x : FrameEquiv Γ Γ' (.kind K) y) ->
  (∃ K', compile_kind Γ' □ K = .ok K' ∧ y = .kind K') := by
intro h
cases h; case _ K' h =>
cases h; exists K'

theorem FrameEquivRefineDataType :
  (x : FrameEquiv Γ Γ' (.tycon K) y) ->
  (∃ K', compile_kind Γ' □ K = .ok K' ∧ y = .datatype K') := by
intro h
cases h; case _ K' _ h =>
cases h; exists K'

@[simp]
abbrev TypeHeadsVarTyType (Γ : HsCtx HsTerm) : (i : JIdx) -> JudgmentType i -> Prop
| .CtxJ => λ () => true
| .TermJ => λ _ => true
| .KindJ => λ _ => true
| .TypeJ => λ (t, k) => ∀ x sp, HsJudgment .TypeJ Γ (t, k) -> t.neutral_form = .some (`#x, sp)
                     -> ∃ T, (Γ s@ x) = .tycon T ∨ (Γ s@ x) = .kind T


theorem type_heads_varty : ⊢s Γ ->
  HsJudgment i Γ jty ->
  TypeHeadsVarTyType Γ i jty := by
intro wf j; induction j <;> simp at *
case _ j _ ih _ _ =>
intro x sp j' tnf
rw[Option.bind_eq_some_iff] at tnf; cases tnf; case _ w tnf =>
cases tnf; case _ h1 h2 =>
injection h2; case _ h2 =>
injection h2; case _ h2 h3 =>
have e : w = (w.1, w.2) := by simp
rw[e] at h1; rw[h2] at h1
replace ih := ih wf x w.2 j h1
assumption




@[simp]
abbrev CompileTypeSoundnessLemmaType (Γ' : Ctx Term): (i : JIdx) -> JudgmentType i -> Prop
| .CtxJ => λ () => true
| .TermJ => λ _ => true
| .KindJ => λ _ => true
| .TypeJ => λ (t, k) => ∃ t' k', (compile_kind Γ' □ k = .ok k' ∧ compile_type Γ' k' t = .ok t' ∧ Γ' ⊢ t' : k')

theorem compile_type_app_soundness {Γ : HsCtx HsTerm} {Γ' : Ctx Term} {T : HsTerm} :
  ⊢s Γ -> ⊢ Γ' -> CtxEquiv Γ Γ' ->
  HsJudgment .KindJ Γ (k, `□) ->
  HsJudgment .TypeJ Γ (T, k) ->
  compile_kind Γ' □ k = .ok k' ->
  T.neutral_form = .some (`#x, sp) ->
  compile_type Γ' k' T = .ok T' ->
  ∃ sp', T'.neutral_form = .some (x, sp') ∧ (∀ t ∈ sp', ∃ k', (Γ' ⊢ t.2 : k'))
  := by
intro wf wf' cc jk jT ck tnf cT
have lem := @hs_neutral_form_well_typed .TypeJ  (T, k) Γ x sp jT
simp at lem;
replace lem := lem tnf
sorry




theorem compile_type_soundness :
  -- still need to find a Prop that characterizes what is the relationship between Γ and Γ'
  ⊢ Γ' ->
  CtxEquiv Γ Γ' ->
  HsJudgment i Γ jty ->
  CompileTypeSoundnessLemmaType Γ' i jty := by
sorry
-- intro wf Γe j
-- induction j generalizing Γ' <;> simp at *

-- case _ ih1 ih2 => -- arrow
--   replace ih1 := @ih1 Γ' wf Γe
--   cases ih1; case _ A' ih1 =>
--   cases ih1; case _ ih1 =>

--   replace ih2 := @ih2 (.empty :: Γ') (by constructor; assumption) (by apply lift_ctx_equiv; assumption)

--   cases ih2; case _ B' ih2 =>
--   cases ih2; case _ ih2 =>
--   exists (A' -t> B')
--   constructor
--   exists A';
--   constructor;
--   case _ => assumption
--   case _ => exists B';
--   constructor; assumption; assumption

-- case _ j1 j2 j3 _ _ ih => -- all
--   have lem := compile_kind_sound_3 wf j2; simp at lem
--   cases lem; case _ A' lem =>
--   cases lem
--   replace ih := @ih (.kind A' :: Γ') (by constructor; assumption; assumption) sorry
--   cases ih; case _ B' ih =>
--   cases ih
--   exists (∀[A']B')
--   constructor;
--   case _ => exists A'; constructor; assumption; exists B'
--   case _ => constructor; assumption; assumption

-- case _ Γ _ _ _ _ j1 j2 j3 ih1 _ ih2 => -- app case
--   replace ih2 := @ih2 Γ' wf Γe
--   cases ih2; case _ T' ih2 =>
--   cases ih2; case _ Tk ih2 =>
--   cases ih2; case _ ih2a ih2b =>
--   cases ih2a; case _ κ ih2a =>
--   cases ih2a; case _ ih2a =>
--   cases ih2a; case _ κ' ih2a =>
--   cases ih2a; case _ ih2a =>
--   cases ih2a
--   cases ih2b

--   replace ih1 := @ih1 Γ' wf Γe
--   cases ih1; case _ A' ih1 =>
--   cases ih1; case _ ih1 =>
--   cases ih1; case _ e1 _ _ _ _ e2 ih1 =>
--   rw[e1] at e2; cases e2
--   cases ih1
--   exists (T' `@k A'); exists κ'
--   constructor
--   case _ => assumption
--   case _ =>
--     split
--     case _ T _ _ _ _ _ _ _ _ _ h =>
--       exfalso; simp at h
--       sorry
--     case _ h =>
--       rw[Option.bind_eq_some_iff] at h
--       cases h; case _ h =>
--       cases h; case _ w h1 h2 =>
--       injection h2; case _ h2 =>
--       injection h2; case _ e1 e2 =>
--       split
--       case _ T k k' A _ _ _ _ _ _ _ sp _ tnfp x =>
--         simp
--         have h1' : w = (w.1, w.2) := by simp
--         rw[h1'] at h1
--         rw[Option.bind_eq_some_iff] at h
--         cases h; case _ tnf =>
--         cases tnf; case _ h1a tnf =>
--         rw[h1] at h1a; cases h1a; rw[e1] at h1;
--         have lem := @hs_neutral_form_well_typed .TypeJ (T, k `-k> k') Γ x w.2 j2
--         simp at lem;
--         replace lem := lem h1
--         cases lem; case _ lem1 lem2 =>
--         cases lem1; case _ K lem1 =>
--         constructor;
--         case _ =>
--           have lem3 := Γe x
--           -- Γ s@ x is a tycon or it is a kind
--           cases lem1;
--           case _ lem1 =>
--             rw[lem1] at lem3;
--             replace lem3 := @FrameEquivRefineType Γ Γ' K (Γ' d@ x) lem3
--             cases lem3; case _ K' lem3 =>
--             exists K'
--             constructor
--             case _ => rw[lem3.2]; unfold Frame.get_type; simp; unfold DsM.toDsM; simp
--             case _ =>
--             split
--             case _ =>
--               split
--               case _ => sorry -- well formed kind always splits. contradiction
--               case _ =>
--                 split
--                 case _ wfk ks ret_k h2 h3 =>
--                   simp at h3; cases h3; case _ h3 h4 =>
--                   cases h3; case _ h3 h5 =>
--                   rw[Option.bind_eq_some_iff] at h2; cases h2; case _ sp' h2 =>
--                   have e := Term.eq_of_beq h3; cases e; clear h3
--                   rw[Except.bind_eq_ok]

--                   sorry
--                 case _ => sorry
--             case _ h =>
--             have lem4 : Γ ⊢s `#x : K := by
--               constructor; assumption; apply Or.inr; assumption
--             -- K' is a wf kind contradiction with h
--             exfalso; sorry
--           case _ lem => sorry

--         sorry
--       case _ =>
--         split <;> simp at *
--         sorry
--         sorry

import Hs.HsTerm
import Hs.Algorithm
import SystemFD.Algorithm

import Aesop

def idHsTerm : HsTerm := `λ{`#0} `#0
def idHsType : HsTerm := `∀{`★} `#0 → `#1

def idTypeKinding : [] ⊢τ idHsType : `★ := by
  unfold idHsType;
  apply HsJudgment.allt;
  case _ => apply HsJudgment.ax (HsJudgment.wfnil)
  case _ =>
    apply HsJudgment.arrow;
    apply HsJudgment.varTy; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
      apply HsJudgment.wfnil; simp; unfold Frame.is_datatype; unfold Frame.apply; simp;
      unfold Frame.is_kind; simp; unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
      {
      apply HsJudgment.ax
      apply HsJudgment.wfkind
      · apply HsJudgment.ax
        apply HsJudgment.wfnil
      · apply HsJudgment.wfnil }

    apply HsJudgment.varTy;
      apply HsJudgment.wfempty; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
      apply HsJudgment.wfnil;
      simp; unfold Frame.is_kind; unfold Frame.apply; simp; unfold Frame.get_type; unfold dnth;
      unfold dnth; unfold Frame.apply; simp;
      {
        apply HsJudgment.ax
        apply HsJudgment.wfempty
        apply HsJudgment.wfkind
        · apply HsJudgment.ax
          apply HsJudgment.wfnil
        · apply HsJudgment.wfnil
      }


def idTyping : [] ⊢t idHsTerm : idHsType := by
 unfold idHsTerm; unfold idHsType;
 apply HsJudgment.implicitAllI;
 apply HsJudgment.lam;
   apply HsJudgment.varTy; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
   apply HsJudgment.wfnil; unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   {
        apply HsJudgment.ax
        apply HsJudgment.wfkind
        · apply HsJudgment.ax
          apply HsJudgment.wfnil
        · apply HsJudgment.wfnil
   };

   apply HsJudgment.var;
   apply HsJudgment.wftype; apply HsJudgment.varTy;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.ax; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
   apply HsJudgment.wfnil; unfold Frame.is_type; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   {
  apply HsJudgment.varTy
  · apply HsJudgment.wfempty
    apply HsJudgment.wfkind
    · apply HsJudgment.ax
      apply HsJudgment.wfnil
    · apply HsJudgment.wfnil
  · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
    apply Or.inr
    rfl
  · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
    rfl
  · apply HsJudgment.ax
    apply HsJudgment.wfempty
    apply HsJudgment.wfkind
    · apply HsJudgment.ax
      apply HsJudgment.wfnil
    · apply HsJudgment.wfnil

   };
   {
  apply HsJudgment.ax
  apply HsJudgment.wfnil
   };
   apply HsJudgment.arrow;
     apply HsJudgment.varTy;
     apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
     unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
     unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
     {
  apply HsJudgment.ax
  apply HsJudgment.wfkind
  · apply HsJudgment.ax
    apply HsJudgment.wfnil
  · apply HsJudgment.wfnil
     };
     apply HsJudgment.varTy;
     apply HsJudgment.wfempty;
     apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; unfold dnth; simp; unfold Frame.apply; simp;
   {
  apply HsJudgment.ax
  apply HsJudgment.wfempty
  apply HsJudgment.wfkind
  · apply HsJudgment.ax
    apply HsJudgment.wfnil
  · apply HsJudgment.wfnil
  };

def idType := compile_type [] idHsType `★ idTypeKinding
def idTerm := compile_term [] idHsTerm idHsType idTyping

#guard idType == .some (∀[★] #0 -t> #1)
#guard idTerm == .some (Λ[★]`λ[#0] #0)
#guard idType == do { let t <- idTerm; infer_type [] t }

#eval idType
#eval idTerm

def MbCtx : Ctx HsTerm :=
  [ .ctor (`∀{`★} `#2 `•k `#0)          -- Nothing :: ∀ a. Maybe a
  , .ctor (`∀{`★} `#0 → `#2 `•k `#1)    -- Just :: ∀ a. a -> Maybe a
  , .datatype (`★ `-k> `★) ]

-- set_option trace.aesop.tree true
-- set_option trace.aesop true
-- def MaybeCtx : HsCtx MbCtx :=
--   .ctor
--     (.ctor
--       (.datatype .nil ⟨`★ `-k> `★ ,
--         by apply HsJudgment.arrowk; apply HsJudgment.ax; apply HsJudgment.wfnil
--            apply HsJudgment.ax; apply HsJudgment.wfnil⟩)
--       ⟨`∀{`★} `#0 → `#2 `•k `#1,
--         by apply HsJudgment.allt
--            apply HsJudgment.ax
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            apply HsJudgment.arrow
--            apply HsJudgment.varTy
--            apply HsJudgment.wfkind
--            apply HsJudgment.ax
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--            apply Or.inr; rfl
--            simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]; rfl
--            apply HsJudgment.appk
--            apply HsJudgment.varTy
--            apply HsJudgment.wfempty
--            apply HsJudgment.wfkind
--            apply HsJudgment.ax
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk;
--              apply HsJudgment.ax; apply HsJudgment.wfnil;
--              apply HsJudgment.ax; apply HsJudgment.wfnil;
--            apply HsJudgment.wfnil
--            simp_all only [dnth, substType_HsTerm, Bool.or_eq_true, Frame.apply_compose, Frame.apply]
--            simp; apply Or.inl; unfold Frame.is_datatype; simp
--            unfold Frame.get_type; unfold dnth; unfold dnth; simp;
--            simp_all only[Frame.apply_compose, Frame.apply]; simp; rfl;
--            apply HsJudgment.varTy
--            apply HsJudgment.wfempty
--            apply HsJudgment.wfkind
--            apply HsJudgment.ax
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfdatatype
--            apply HsJudgment.arrowk
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.ax
--            apply HsJudgment.wfnil
--            apply HsJudgment.wfnil
--            simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--            apply Or.inr; rfl
--            simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]; rfl
--            {
--                 apply HsJudgment.ax
--                 apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--            }
--            {
--                 apply HsJudgment.ax
--                 apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--            }
--       ⟩)
--     ⟨`∀{`★} `#2 `•k `#0, by
--       apply HsJudgment.allt
--       apply HsJudgment.ax;
--         apply HsJudgment.wfctor;
--         { apply HsJudgment.allt;
--           apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           apply HsJudgment.arrow
--           apply HsJudgment.varTy
--           apply HsJudgment.wfkind
--           apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--           apply Or.inr; rfl;
--           simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]; rfl;
--           apply HsJudgment.appk
--           apply HsJudgment.varTy
--           apply HsJudgment.wfempty
--           apply HsJudgment.wfkind
--           apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--           apply Or.inl; rfl
--           simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]; rfl;

--           -- simp_all only [Function.comp_apply, HsTerm.subst_const]
--           apply HsJudgment.varTy
--           apply HsJudgment.wfempty
--           apply HsJudgment.wfkind
--           apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfdatatype
--           apply HsJudgment.arrowk
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.ax
--           apply HsJudgment.wfnil
--           apply HsJudgment.wfnil
--           simp_all only [dnth, substType_HsTerm, Bool.or_eq_true, Frame.apply, Frame.is_kind]
--           apply Or.inr; simp;
--           simp_all only [dnth, Frame.get_type_apply_commute, Option.map_map, Frame.get_type];
--           unfold Frame.apply; simp;
--           {
--                 simp_all only [HsTerm.smap, HsTerm.smap.eq_3]
--                 apply HsJudgment.ax
--                 apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--           };
--           {
--                 apply HsJudgment.ax
--                 apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--           }};
--         apply HsJudgment.wfdatatype;   apply HsJudgment.arrowk; apply HsJudgment.ax;
--         apply HsJudgment.wfnil; apply HsJudgment.ax; apply HsJudgment.wfnil; apply HsJudgment.wfnil;
--         apply ValidHsCtorType.all; apply ValidHsCtorType.arrow; apply ValidHsCtorType.refl;
--         unfold HsValidHeadVariable; simp; rfl
--       apply HsJudgment.appk;
--         apply HsJudgment.varTy;
--           apply HsJudgment.wfkind;
--             apply HsJudgment.ax;
--             {
--               apply HsJudgment.wfctor;
--               {
--                 apply HsJudgment.allt
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.arrow
--                   · apply HsJudgment.varTy
--                     · apply HsJudgment.wfkind
--                       · apply HsJudgment.ax
--                         apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                       · apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                     · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                       apply Or.inr
--                       rfl
--                     · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]
--                       rfl
--                   · apply HsJudgment.appk
--                     on_goal 2 => {
--                       apply HsJudgment.varTy
--                       · apply HsJudgment.wfempty
--                         apply HsJudgment.wfkind
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                         · apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                       · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                         apply Or.inr
--                         rfl
--                       · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                         rfl
--                     }
--                     · simp_all only [Function.comp_apply, HsTerm.subst_const]
--                       apply HsJudgment.varTy
--                       · apply HsJudgment.wfempty
--                         apply HsJudgment.wfkind
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                         · apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil

--                       · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]; apply Or.inl; rfl
--                       · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                         rfl
--               };
--               {
--                 apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--               };
--               {
--                 apply ValidHsCtorType.all; apply ValidHsCtorType.arrow;
--                 apply ValidHsCtorType.refl; unfold HsValidHeadVariable; simp;
--                 simp_all only [Frame.apply, Frame.is_datatype];
--               };
--             };
--             apply HsJudgment.wfctor;
--             apply HsJudgment.allt;
--             {
--                 apply HsJudgment.ax
--                 apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--             };
--             {
--                 apply HsJudgment.arrow
--                 · apply HsJudgment.varTy
--                   · apply HsJudgment.wfkind
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfdatatype
--                       · apply HsJudgment.arrowk
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfnil
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfnil
--                       · apply HsJudgment.wfnil
--                     · apply HsJudgment.wfdatatype
--                       · apply HsJudgment.arrowk
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfnil
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfnil
--                       · apply HsJudgment.wfnil
--                   · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]; apply Or.inr; rfl
--                   · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]; rfl
--                 · apply HsJudgment.appk
--                   · apply HsJudgment.varTy
--                     · apply HsJudgment.wfempty
--                       apply HsJudgment.wfkind
--                       · apply HsJudgment.ax
--                         apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                       · apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                     · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                       apply Or.inl; rfl
--                     · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]; rfl
--                   · simp_all only [HsTerm.smap, HsTerm.smap.eq_3]
--                     apply HsJudgment.varTy
--                     · apply HsJudgment.wfempty
--                       apply HsJudgment.wfkind
--                       · apply HsJudgment.ax
--                         apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                       · apply HsJudgment.wfdatatype
--                         · apply HsJudgment.arrowk
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                           · apply HsJudgment.ax
--                             apply HsJudgment.wfnil
--                         · apply HsJudgment.wfnil
--                     · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                       apply Or.inr
--                       rfl
--                     · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                       rfl
--                   {
--                         simp_all only [HsTerm.smap]
--                         apply HsJudgment.ax
--                         apply HsJudgment.wfempty
--                         apply HsJudgment.wfkind
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                         · apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                   }
--                   {
--                         apply HsJudgment.ax
--                         apply HsJudgment.wfempty
--                         apply HsJudgment.wfkind
--                         · apply HsJudgment.ax
--                           apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                         · apply HsJudgment.wfdatatype
--                           · apply HsJudgment.arrowk
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                             · apply HsJudgment.ax
--                               apply HsJudgment.wfnil
--                           · apply HsJudgment.wfnil
--                   }
--             };
--             apply HsJudgment.wfdatatype;
--             apply HsJudgment.arrowk;
--             apply HsJudgment.ax; apply HsJudgment.wfnil;
--             apply HsJudgment.ax; apply HsJudgment.wfnil;
--             apply HsJudgment.wfnil;
--             apply ValidHsCtorType.all; apply ValidHsCtorType.arrow;
--             apply ValidHsCtorType.refl; unfold HsValidHeadVariable; simp;
--             simp_all only [Frame.apply, Frame.is_datatype];
--           simp; apply Or.inl; rfl;
--           unfold Frame.get_type; unfold dnth; unfold Frame.apply; unfold dnth;
--           simp; unfold Frame.apply; simp; rfl;
--         apply HsJudgment.varTy;
--           {apply HsJudgment.wfkind;
--             apply HsJudgment.ax;
--             {apply HsJudgment.wfctor;
--               {
--         apply HsJudgment.allt
--         · apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           · apply HsJudgment.arrowk
--             · apply HsJudgment.ax
--               apply HsJudgment.wfnil
--             · apply HsJudgment.ax
--               apply HsJudgment.wfnil
--           · apply HsJudgment.wfnil
--         · apply HsJudgment.arrow
--           · apply HsJudgment.varTy
--             · apply HsJudgment.wfkind
--               · apply HsJudgment.ax
--                 apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--               · apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--             · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--               apply Or.inr
--               rfl
--             · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]
--               rfl
--           · apply HsJudgment.appk
--             on_goal 2 => {
--               apply HsJudgment.varTy
--               · apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--               · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                 apply Or.inr
--                 rfl
--               · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                 rfl
--             }
--             · simp_all only [Function.comp_apply, HsTerm.subst_const]
--               apply HsJudgment.varTy
--               · apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--               · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                 apply Or.inl
--                 rfl
--               · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                 rfl};
--               apply HsJudgment.wfdatatype;
--               apply HsJudgment.arrowk;
--               apply HsJudgment.ax;
--               apply HsJudgment.wfnil;
--               apply HsJudgment.ax;
--               apply HsJudgment.wfnil;
--               apply HsJudgment.wfnil;
--               {
--                 apply ValidHsCtorType.all; apply ValidHsCtorType.arrow;
--                 apply ValidHsCtorType.refl; unfold HsValidHeadVariable; simp;
--                 simp_all only [Frame.apply, Frame.is_datatype];
--               }
--             };
--             { apply HsJudgment.wfctor;
--               {
--         apply HsJudgment.allt
--         · apply HsJudgment.ax
--           apply HsJudgment.wfdatatype
--           · apply HsJudgment.arrowk
--             · apply HsJudgment.ax
--               apply HsJudgment.wfnil
--             · apply HsJudgment.ax
--               apply HsJudgment.wfnil
--           · apply HsJudgment.wfnil
--         · apply HsJudgment.arrow
--           · apply HsJudgment.varTy
--             · apply HsJudgment.wfkind
--               · apply HsJudgment.ax
--                 apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--               · apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil
--             · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--               apply Or.inr
--               rfl
--             · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute]
--               rfl
--           · apply HsJudgment.appk
--             on_goal 2 => {
--               apply HsJudgment.varTy
--               · apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--               · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                 apply Or.inr
--                 rfl
--               · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                 rfl
--             }
--             · simp_all only [Function.comp_apply, HsTerm.subst_const]
--               apply HsJudgment.varTy
--               · apply HsJudgment.wfempty
--                 apply HsJudgment.wfkind
--                 · apply HsJudgment.ax
--                   apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--                 · apply HsJudgment.wfdatatype
--                   · apply HsJudgment.arrowk
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                     · apply HsJudgment.ax
--                       apply HsJudgment.wfnil
--                   · apply HsJudgment.wfnil
--               · simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]
--                 apply Or.inl
--                 rfl
--               · simp_all only [dnth, substType_HsTerm, Frame.get_type_apply_commute, Option.map_map]
--                 rfl
--               };
--               { apply HsJudgment.wfdatatype
--                 · apply HsJudgment.arrowk
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                   · apply HsJudgment.ax
--                     apply HsJudgment.wfnil
--                 · apply HsJudgment.wfnil };
--               {
--                 apply ValidHsCtorType.all; apply ValidHsCtorType.arrow;
--                 apply ValidHsCtorType.refl; unfold HsValidHeadVariable; simp;
--                 simp_all only [Frame.apply, Frame.is_datatype]
--               }
--           }};
--           { simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]; apply Or.inr; rfl};
--           { simp_all only [dnth, substType_HsTerm, Bool.or_eq_true]; rfl };
--           {
--             sorry
--           };
--           {
--             sorry
--           }
--     ⟩

-- #eval compile_ctx MaybeCtx
-- #guard compile_ctx MaybeCtx == .some [ .ctor (∀[★](#2 `@k #0))
--                                      , .ctor (∀[★]#0 -t> (#2 `@k #1))
--                                      , .datatype (★ -k> ★) ]

-- #guard compile .ctx MbCtx MaybeCtx == compile_ctx MaybeCtx
#guard compile .type [] ⟨(idHsType, `★), idTypeKinding⟩ == compile_type [] idHsType `★ idTypeKinding
#guard compile .term [] ⟨(idHsTerm, idHsType), idTyping⟩ == compile_term [] idHsTerm idHsType idTyping

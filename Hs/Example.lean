import Hs.HsTerm
import Hs.Algorithm
import SystemFD.Algorithm

def idHsTerm : HsTerm := `λ{`#0} `#0
def idHsType : HsTerm := `∀{`★} `#0 → `#1

def idTypeKinding : [] ⊢τ idHsType : `★ := by
  unfold idHsType;
  apply HsJudgment.allt;
  case _ => apply HsJudgment.ax (HsJudgment.wfnil)
  case _ =>
    apply HsJudgment.arrow;
    case _ =>
      apply HsJudgment.varTy; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
      apply HsJudgment.wfnil; simp; unfold Frame.is_datatype; unfold Frame.apply; simp;
      unfold Frame.is_kind; simp; unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
    case _ =>
      apply HsJudgment.varTy;
      apply HsJudgment.wfempty; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
      apply HsJudgment.wfnil;
      simp; unfold Frame.is_kind; unfold Frame.apply; simp; unfold Frame.get_type; unfold dnth;
      unfold dnth; unfold Frame.apply; simp

def idTyping : [] ⊢t idHsTerm : idHsType := by
 unfold idHsTerm; unfold idHsType;
 apply HsJudgment.implicitAllI;
 apply HsJudgment.lam;
   apply HsJudgment.varTy; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
   apply HsJudgment.wfnil; unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.var;
   apply HsJudgment.wftype; apply HsJudgment.varTy;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
   apply HsJudgment.wfnil; unfold Frame.is_type; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.arrow;
   apply HsJudgment.varTy;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.varTy;
   apply HsJudgment.wfempty;
   apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
   unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp; unfold Frame.apply; simp;
   unfold Frame.get_type; unfold dnth; unfold Frame.apply; unfold dnth; simp; unfold Frame.apply; simp;
   apply HsJudgment.ax (HsJudgment.wfnil);
   apply HsJudgment.arrow;
   apply HsJudgment.varTy;
      apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil); apply HsJudgment.wfnil;
      unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp;
      unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp;
   apply HsJudgment.varTy;
      apply HsJudgment.wfempty; apply HsJudgment.wfkind; apply HsJudgment.ax (HsJudgment.wfnil);
      apply HsJudgment.wfnil;
      unfold Frame.is_kind; unfold dnth; unfold Frame.apply; simp; unfold Frame.apply; simp;
      unfold Frame.get_type; unfold dnth; unfold Frame.apply; simp; unfold Frame.apply; simp;

def idType := compile_type [] idHsType `★ idTypeKinding
def idTerm := compile_term [] idHsTerm idHsType idTyping

#guard idType == .some (∀[★] #0 -t> #1)
#guard idTerm == .some (Λ[★]`λ[#0] #0)
#guard idType == do { let t <- idTerm; infer_type [] t }

#eval idType
#eval idTerm

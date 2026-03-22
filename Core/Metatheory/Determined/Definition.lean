import LeanSubst
import Core.Term
import Core.Reduction
import Core.Typing

open LeanSubst

namespace Core

def Term.Determined (t : Term) : Prop :=
  VariantMissing [.ctor2 .choice, .ctor0 .zero, .guard] t

def SpineElem.Determined : SpineElem -> Prop
| type _ => True
| term t => t.Determined
| oterm t => t.Determined

def Determined.openm (G : List Global) (x : String) : Prop :=
  ∀ Δ Γ T B sp,
    lookup x G = some (.openm x T) ->
    G&Δ,Γ ⊢ (g#x).apply sp : B ->
    sp.length ≥ T.arity ->
    (∀ e ∈ sp, ∀ t, .oterm t = e -> t.spine.isSome) ->
    (∀ e ∈ sp, ∀ t, .oterm t = e -> Value G t) ->
    (∀ e ∈ sp, e.Determined) ->
    ∃ t, Plus (Red G) ((g#x).apply sp) t ∧ Term.Determined t

def Determined.defn (G : List Global) (x : String) : Prop :=
  ∀ T t,
    lookup x G = some (.defn x T t) ->
    Term.Determined t

def Global.Determined (G : List Global) : Prop :=
  ∀ x, Determined.openm G x ∧ Determined.defn G x

theorem Term.Determined.var : (#x).Determined := by
  unfold Term.Determined; apply VariantMissing.var

theorem Term.Determined.global : (g#x).Determined := by
  unfold Term.Determined; apply VariantMissing.global

theorem Term.Determined.lam : t.Determined -> (λ[A] t).Determined := by
  intro h; unfold Term.Determined; apply VariantMissing.lam; apply h

theorem Term.Determined.lamt : t.Determined -> (Λ[A] t).Determined := by
  intro h; unfold Term.Determined; apply VariantMissing.tbind _ h;
  intro h';
  cases h'; case _ h => cases h; case _ h => cases h; case _ h => cases h

theorem Term.Determined.app {b: BaseKind} {f a : Term} : f.Determined ∧ a.Determined <-> (f •(b) a).Determined := by
  apply Iff.intro <;> intro h
  unfold Term.Determined; apply VariantMissing.ctor2 _ h.1 h.2
  intro h'; cases h'; case _ h => cases h; case _ h => cases h; case _ h => cases h
  cases h; unfold Determined; simp [*]

theorem Term.Determined.appt {f: Term} {a : Ty} : f.Determined -> (f •[ a ]).Determined := by
  intro h1
  unfold Term.Determined; apply VariantMissing.ctor1 _ h1
  intro h'; cases h'; case _ h => cases h; case _ h => cases h; case _ h => cases h

theorem Term.Determined.cast {t c: Term} : t.Determined ∧ c.Determined <-> (t ▹ c).Determined := by
  apply Iff.intro <;> intro h
  unfold Term.Determined; apply VariantMissing.ctor2 _ h.1 h.2
  intro h'; cases h'; case _ h => cases h; case _ h => cases h; case _ h => cases h
  cases h; unfold Determined; simp [*]

theorem Term.Determined.refl : (refl! T).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor0; intro h
  simp at h; cases h; case _ h => cases h
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h

theorem Term.Determined.sym : c.Determined -> (sym! c).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor1; intro h
  simp at h; cases h; case _ h => cases h -- TODO: Macro this?
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h

theorem Term.Determined.trans : c1.Determined -> c2.Determined -> (c1 `; c2).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor2; intro h
  simp at h; cases h; case _ h => cases h
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h


theorem Term.Determined.fst : c.Determined -> (fst! c).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor1; intro h
  simp at h; cases h; case _ h => cases h
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h


theorem Term.Determined.snd : c.Determined -> (snd! c).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor1; intro h
  simp at h; cases h; case _ h => cases h
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h

theorem Term.Determined.appc : c1.Determined -> c2.Determined -> (c1 •c c2).Determined := by
  unfold Term.Determined; apply VariantMissing.ctor2; intro h
  simp at h; cases h; case _ h => cases h
  case _ h =>
    cases h
    case _ h => cases h
    case _ h => cases h


theorem Term.Determined.match {s d : Term} {ps cs : Vect n Term}:
  s.Determined ->
  d.Determined ->
  (∀ i, (ps i).Determined) ->
  (∀ i, (cs i).Determined) ->
  (match! n s ps cs d).Determined
:= by
  intro h1 h2 h3 h4
  unfold Term.Determined; apply VariantMissing.mtch; repeat assumption

theorem Term.Determined.spine {h : Term} {sp : List SpineElem} :
       h.Determined -> (∀ e ∈ sp, e.Determined) ->
       (h.apply sp).Determined := by
intro h1 h2
induction sp using List.reverse_ind generalizing h <;> simp [Term.apply] at *
case nil => assumption
case rcons hd tl ih =>
cases hd
case type =>
  rw[<-Spine.apply_type];
  apply Determined.appt
  apply ih h1
  intro e; replace h2 := h2 e;
  intro h; replace h2 := h2 (Or.inl h)
  apply h2
case term x =>
  rw[<-Spine.apply_term];
  apply Determined.app.1
  apply And.intro
  · apply ih h1
    intro e; replace h2 := h2 e;
    intro h; replace h2 := h2 (Or.inl h)
    apply h2
  · replace h2 := h2 (.term x); simp at h2;
    unfold SpineElem.Determined at h2; simp at h2; apply h2
case oterm x =>
  rw[<-Spine.apply_oterm];
  apply Determined.app.1
  apply And.intro
  · apply ih h1
    intro e; replace h2 := h2 e;
    intro h; replace h2 := h2 (Or.inl h)
    apply h2
  · replace h2 := h2 (.oterm x); simp at h2;
    unfold SpineElem.Determined at h2; simp at h2; apply h2
end Core

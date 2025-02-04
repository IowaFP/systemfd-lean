import SystemFD.Term
import SystemFD.Ctx

@[simp]
def prefix_equal [BEq T] : List T -> List T -> Option (List T)
| [], t => .some t
| .cons _ _, [] => .none
| .cons x1 t1, .cons x2 t2 => if x1 == x2 then prefix_equal t1 t2 else .none

inductive Red : Ctx Term -> List Term -> List Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red Γ (((`λ[A] b) `@ t) :: tl) (b β[t] :: tl)
| betat : Red Γ (((Λ[A] b) `@t t) :: tl) (b β[t] :: tl)
| cast : Red Γ ((t ▹ refl! A) :: tl) (t :: tl)
| sym : Red Γ ((sym! (refl! A)) :: tl) ((refl! A) :: tl)
| seq : Red Γ (((refl! A) `; (refl! A)) :: tl) ((refl! A) :: tl)
| appc : Red Γ ((refl! (A -k> B) `@c (refl! A)) :: tl) ((refl! B) :: tl)
| fst : Red Γ ((.ctor1 .fst (refl! (A `@k B))) :: tl) ((refl! A) :: tl)
| snd : Red Γ ((.ctor1 .snd (refl! (A `@k B))) :: tl) ((refl! B) :: tl)
| allc : Red Γ ((∀c[A] refl! B) :: tl) ((refl! (∀[A] B)) :: tl)
| arrowc : Red Γ ((refl! A -c> refl! B) :: tl) ((refl! (A -t> B)) :: tl)
----------------------------------------------------------------
---- Ite matching
----------------------------------------------------------------
| ite_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Red Γ (.ite p s b e :: tl) (b.apply_spine q :: tl)
| ite_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  x ≠ x' ∨ prefix_equal sp sp' = .none ->
  Red Γ (.ite p s b e :: tl) (e :: tl)
----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Red Γ (.guard p s b :: tl) (b.apply_spine q :: tl)
| guard_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  x ≠ x' ∨ prefix_equal sp sp = .none ->
  Red Γ (.guard p s b :: tl) tl
----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
| inst :
  .some x = Term.neutral_head h ->
  indices = instance_indices Γ 0 x ->
  indices.length > 0 ->
  Δ = tl ++ (instantiate_instances Γ indices x h) ->
  Red Γ (h::tl) Δ
----------------------------------------------------------------
---- Contextual/Congruence rules
----------------------------------------------------------------
| tail : Red Γ tl tl' -> Red Γ (h::tl) (h::tl')
| app_congr1 : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@ a) :: tl) ((f' `@ a) :: tl)
| app_congr2 : Red Γ (a::tl) (a'::tl) -> Red Γ ((f `@ a) :: tl) ((f `@ a') :: tl)
| appt_congr : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@t a) :: tl) ((f' `@ a) :: tl)
| cast_congr : Red Γ (e::tl) (e'::tl) -> Red Γ ((t ▹ e)::tl) ((t ▹ e')::tl)
| ite_congr : Red Γ (s::tl) (s'::tl) -> Red Γ ((.ite p s b e)::tl) ((.ite p s' b e)::tl)
| sym_congr : Red Γ (e::tl) (e'::tl) -> Red Γ ((sym! e)::tl) ((sym! e')::tl)
| seq_congr1 : Red Γ (u::tl) (u'::tl) -> Red Γ ((u `; v)::tl) ((u' `; v)::tl)
| seq_congr2 : Red Γ (v::tl) (v'::tl) -> Red Γ ((u `; v)::tl) ((u `; v')::tl)
| arrowc_congr1 : Red Γ (u::tl) (u'::tl) -> Red Γ ((u -c> v)::tl) ((u' -c> v)::tl)
| arrowc_congr2 : Red Γ (v::tl) (v'::tl) -> Red Γ ((u -c> v)::tl) ((u -c> v')::tl)
| appc_congr1 : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@c a)::tl) ((f' `@c a)::tl)
| appc_congr2 : Red Γ (a::tl) (a'::tl) -> Red Γ ((f `@c a)::tl) ((f `@c a')::tl)
| fst_congr : Red Γ (u::tl) (u'::tl) -> Red Γ ((.ctor1 .fst u)::tl) ((.ctor1 .fst u')::tl)
| snd_congr : Red Γ (u::tl) (u'::tl) -> Red Γ ((.ctor1 .snd u)::tl) ((.ctor1 .snd u')::tl)
| apptc_congr1 : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@c[a])::tl) ((f' `@c[a])::tl)
| apptc_congr2 : Red Γ (a::tl) (a'::tl) -> Red Γ ((f `@c[a])::tl) ((f `@c[a'])::tl)
| allc_congr : Red Γ (e::tl) (e'::tl) -> Red Γ ((∀c[A] e)::tl) ((∀c[A] e')::tl)
| guard_congr : Red Γ (s::tl) (s'::tl) -> Red Γ ((.guard p s b)::tl) ((.guard p s' b)::tl)
| letopentype_congr : Red (.opent A :: Γ) (b::tl) (b'::tl) -> Red Γ ((letopentype! A b)::tl) ((letopentype! A b')::tl)
| letopen_congr : Red (.openm A :: Γ) (b::tl) (b'::tl) -> Red Γ ((letopen! A b)::tl) ((letopen! A b')::tl)
| letdata_congr : Red (.datatype A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.letdata A b)::tl) ((.letdata A b')::tl)
| letctor_congr : Red (.ctor A :: Γ) (b::tl) (b'::tl) -> Red Γ ((letctor! A b)::tl) ((letctor! A b')::tl)
| insttype_congr : Red (.insttype A :: Γ) (b::tl) (b'::tl) -> Red Γ ((insttype! A b)::tl) ((insttype! A b')::tl)
| inst_congr : Red (.inst x A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.inst x A b)::tl) ((.inst x A b')::tl)

import SystemFD.Term
import SystemFD.Ctx

inductive Red : Ctx Term -> List Term -> List Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red Γ (((`λ[A] b) `@ t) :: tl) (b β[t] :: tl)
| betat : Red Γ (((Λ[A] b) `@t t) :: tl) (b β[t] :: tl)
| cast : Red Γ ((t ▹ .refl A) :: tl) (t :: tl)
| sym : Red Γ ((.sym (.refl A)) :: tl) ((.refl A) :: tl)
| seq : Red Γ (((.refl A) `; (.refl A)) :: tl) ((.refl A) :: tl)
| appc : Red Γ ((.refl (A -k> B) `@c (.refl A)) :: tl) ((.refl B) :: tl)
| fst : Red Γ ((.fst (.refl (A `@k B))) :: tl) ((.refl A) :: tl)
| snd : Red Γ ((.snd (.refl (A `@k B))) :: tl) ((.refl B) :: tl)
| allc : Red Γ ((∀c[A] .refl B) :: tl) ((.refl (∀[A] B)) :: tl)
----------------------------------------------------------------
---- Case matching
----------------------------------------------------------------
| branch_nil : Red Γ ((.case t .nil) :: tl) tl
| branch_cons_matched :
  .some x = Term.neutral_head t ->
  .some x = Term.neutral_head c ->
  .some σ = Term.neutral_subst t ->
  Red Γ ((.case t (.cons (.branch c n m) br)) :: tl) ([σ]m :: tl)
| branch_cons_missed :
  .some x = Term.neutral_head t ->
  .some y = Term.neutral_head c ->
  x ≠ y ->
  Red Γ ((.case t (.cons (.branch c n m) br)) :: tl) ((.case t br) :: tl)
----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  .some x = Term.neutral_head m ->
  .some x = Term.neutral_head s ->
  .some σ = Term.neutral_subst m ->
  Red Γ ((.guard s n m t) :: tl) ([σ]t :: tl)
| guard_missed :
  .some x = Term.neutral_head m ->
  .some y = Term.neutral_head s ->
  x ≠ y ->
  Red Γ ((.guard s n m t) :: tl) tl
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
| case_congr : Red Γ (s::tl) (s'::tl) -> Red Γ ((.case s br)::tl) ((.case s' br)::tl)
| sym_congr : Red Γ (e::tl) (e'::tl) -> Red Γ ((.sym e)::tl) ((.sym e')::tl)
| seq_congr1 : Red Γ (u::tl) (u'::tl) -> Red Γ ((u `; v)::tl) ((u' `; v)::tl)
| seq_congr2 : Red Γ (v::tl) (v'::tl) -> Red Γ ((u `; v)::tl) ((u `; v')::tl)
| appc_congr1 : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@c a)::tl) ((f' `@c a)::tl)
| appc_congr2 : Red Γ (a::tl) (a'::tl) -> Red Γ ((f `@c a)::tl) ((f `@c a')::tl)
| fst_congr : Red Γ (u::tl) (u'::tl) -> Red Γ ((.fst u)::tl) ((.fst u')::tl)
| snd_congr : Red Γ (u::tl) (u'::tl) -> Red Γ ((.snd u)::tl) ((.snd u')::tl)
| apptc_congr1 : Red Γ (f::tl) (f'::tl) -> Red Γ ((f `@c[a])::tl) ((f' `@c[a])::tl)
| apptc_congr2 : Red Γ (a::tl) (a'::tl) -> Red Γ ((f `@c[a])::tl) ((f `@c[a'])::tl)
| allc_congr : Red Γ (e::tl) (e'::tl) -> Red Γ ((∀c[A] e)::tl) ((∀c[A] e')::tl)
| guard_congr : Red Γ (m::tl) (m'::tl) -> Red Γ ((.guard s n m t)::tl) ((.guard s n m' t)::tl)
| letopentype_congr : Red (.opent A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.letopentype A b)::tl) ((.letopentype A b')::tl)
| letopen_congr : Red (.openm A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.letopen A b)::tl) ((.letopen A b')::tl)
| letdata_congr : Red (.datatype A n :: Γ) (b::tl) (b'::tl) -> Red Γ ((.letdata A n b)::tl) ((.letdata A n b')::tl)
| letctor_congr : Red (.ctor A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.letctor A b)::tl) ((.letctor A b')::tl)
| insttype_congr : Red (.insttype A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.insttype A b)::tl) ((.insttype A b')::tl)
| inst_congr : Red (.inst x A :: Γ) (b::tl) (b'::tl) -> Red Γ ((.inst x A b)::tl) ((.inst x A b')::tl)

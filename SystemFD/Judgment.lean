
import SystemFD.Term
import SystemFD.Ctx

inductive JudgmentVariant where
| wf | wfctor | prf | bchl | bch | ctors

@[simp]
abbrev JudgmentArgs : JudgmentVariant -> Type
| .wf => Unit
| .wfctor => Nat
| .prf => Term × Term
| .bchl => Term × Term × Term
| .bch => Term × Term × Term
| .ctors => Term × Nat × Term

inductive Judgment : (v : JudgmentVariant) -> Ctx Term -> JudgmentArgs v -> Prop where
--------------------------------------------------------------------------------------
---- Well-Formed Contexts
--------------------------------------------------------------------------------------
| empty :  Judgment .wf [] ()
| wftype :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.type A::Γ) ()
| wfkind :
  Judgment .prf Γ (A, .kind) ->
  Judgment .wf Γ () ->
  Judgment .wf (.kind A::Γ) ()
| wfdatatype :
  Judgment .prf Γ (A, .kind) ->
  Judgment .wfctor Γ n ->
  Judgment .wf (.datatype A n::Γ) ()
| wfctor0 :
  Judgment .wf Γ () ->
  Judgment .wfctor Γ 0
| wfctor :
  Judgment .prf Γ (A, ★) ->
  Judgment .wfctor Γ n ->
  Judgment .wfctor (.ctor A::Γ) (n + 1)
| wfopent :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.opent A::Γ) ()
| wfopenm :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.openm A::Γ) ()
| wfinsttype :
  Judgment .prf Γ (A, .const K) ->
  Judgment .wf Γ () ->
  Judgment .wf (.insttype A::Γ) ()
| wfinst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t, T) ->
  Judgment .wf (.inst x t::Γ) ()
--------------------------------------------------------------------------------------
---- Declarations
--------------------------------------------------------------------------------------
| letdata :
  Judgment .prf Γ (T, .kind) ->
  Judgment .ctors (.datatype T n::Γ) (t, n, A) ->
  Judgment .prf Γ (.letdata T n t, A)
| letctor0 :
  Judgment .prf Γ (t, A) ->
  Judgment .ctors Γ (t, 0, A)
| letctor :
  Judgment .prf Γ (T, ★) ->
  Judgment .ctors (.ctor T::Γ) (t, n, A) ->
  Judgment .ctors Γ (.letctor T t, n + 1, A)
| letopentype :
  Judgment .prf Γ (T, .kind) ->
  Judgment .prf (.opent T::Γ) (t, A) ->
  Judgment .prf Γ (.letopentype T t, A)
| letopen :
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf (.openm T::Γ) (t, A) ->
  Judgment .prf Γ (.letopen T t, A)
| insttype :
  Judgment .prf Γ (T, .const K) ->
  Judgment .prf (.insttype T::Γ) (t, A) ->
  Judgment .prf Γ (.insttype T t, A)
| inst :
  .openm T = Γ d@ x ->
  Judgment .prf Γ (t1, T) ->
  Judgment .prf (.inst x t1::Γ) (t2, A) ->
  Judgment .prf Γ (.inst x t1 t2, A)
--------------------------------------------------------------------------------------
---- Kind/Type Constructor Judgments
--------------------------------------------------------------------------------------
| ax :
  Judgment .wf Γ () ->
  Judgment .prf Γ (.const K, .kind)
| var :
  Judgment .wf Γ () ->
  .some T = Frame.get_type (Γ d@ x) ->
  Judgment .prf Γ (#x, T)
| allk :
  Judgment .prf Γ (A, .kind) ->
  Judgment .prf Γ (B, .kind) ->
  Judgment .prf Γ (A -k> B, .kind)
| allt :
  Judgment .prf Γ (A, .kind) ->
  Judgment .prf (.kind A::Γ) (B, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (∀[A] B, K)
| arrow :
  Judgment .prf Γ (A, ★) ->
  Judgment .prf Γ (B, ★) ->
  Judgment .prf Γ (A -t> B, ★)
| appk :
  Judgment .prf Γ (f, A -k> B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@k a, B)
--------------------------------------------------------------------------------------
---- Datatype case expressions
--------------------------------------------------------------------------------------
| case :
  Judgment .prf Γ (m, A) ->
  Judgment .prf Γ (A, ★) ->
  Judgment .bchl Γ (br, A, B) ->
  Judgment .prf Γ (.case m br, B)
| branchstart :
  Judgment .bch Γ (t, A, B) ->
  Judgment .bchl Γ (.cons t .nil, A, B)
| branchcons :
  Judgment .bch Γ (hd, A, B) ->
  Judgment .bchl Γ (tl, A, B) ->
  Judgment .bchl Γ (.cons hd tl, A, B)
| branch0 :
  Judgment .prf Γ (c, A) ->
  .some ctorid = Term.neutral_head c ->
  .some dataid = Term.neutral_head A ->
  is_datatype Γ ctorid dataid ->
  Judgment .prf Γ (t, B) ->
  Judgment .bch Γ (.branch c 0 t, A, B)
| branch_arrow :
  Judgment .prf Γ (c, C -t> D) ->
  Judgment .bch (.type C::Γ) (.branch ([S]c `@ #0) n t, A, B) ->
  Judgment .bch Γ (.branch c (n + 1) t, A, B)
| branch_all :
  Judgment .prf Γ (c, ∀[C] D) ->
  Judgment .bch (.kind C::Γ) (.branch ([S]c `@t #0) n t, A, B) ->
  Judgment .bch Γ (.branch c (n + 1) t, A, B)
--------------------------------------------------------------------------------------
---- Guards
--------------------------------------------------------------------------------------
| guard0 :
  Judgment .prf Γ (s, A) ->
  .some openmid = Term.neutral_head s ->
  Judgment .prf Γ (m, A) ->
  Judgment .prf Γ (A, ◯) ->
  Judgment .prf Γ (t, B) ->
  Judgment .prf Γ (.guard s 0 m t, B)
| guard_arrow :
  Judgment .prf Γ (s, C -t> D) ->
  Judgment .prf (.type C::Γ) (.guard ([S]s `@ #0) n ([S]m) t, B) ->
  Judgment .prf Γ (.guard s (n + 1) m t, B)
| guard_all :
  Judgment .prf Γ (s, ∀[C] D) ->
  Judgment .prf (.kind C::Γ) (.guard ([S]s `@t #0) n ([S]m) t, B) ->
  Judgment .prf Γ (.guard s (n + 1) m t, B)
--------------------------------------------------------------------------------------
---- Terms
--------------------------------------------------------------------------------------
| lam :
  Judgment .prf Γ (A, .const K) ->
  Judgment .prf (.type A::Γ) (t, B) ->
  Judgment .prf Γ (`λ[A] t, A -t> b)
| app :
  Judgment .prf Γ (f, A -t> B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@ a, B)
| lamt :
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf (.kind A::Γ) (t, B) ->
  Judgment .prf Γ (Λ[A] t, B)
| appt :
  Judgment .prf Γ (f, ∀[A] B) ->
  Judgment .prf Γ (a, A) ->
  Judgment .prf Γ (f `@t a, B)
| cast :
  Judgment .prf Γ (t, A) ->
  Judgment .prf Γ (c, A ~ B) ->
  Judgment .prf Γ (t ▹ c, B)
--------------------------------------------------------------------------------------
---- Coercions
--------------------------------------------------------------------------------------
| refl :
  Judgment .prf Γ (A, K) ->
  Judgment .prf Γ (K, .kind) ->
  Judgment .prf Γ (.refl A, A)
| sym :
  Judgment .prf Γ (t, A ~ B) ->
  Judgment .prf Γ (.sym t, B ~ A)
| seq :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, B ~ C) ->
  Judgment .prf Γ (t1 `; t2, A ~ C)
| appc :
  Judgment .prf Γ (t1, A ~ B) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c t2, (A `@k C) ~ (B `@k D))
| fst :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (.fst t, A ~ B)
| snd :
  Judgment .prf Γ (t, (A `@k C) ~ (B `@k D)) ->
  Judgment .prf Γ (.snd t, C ~ D)
| allc :
  Judgment .prf Γ (t, A ~ B) ->
  Judgment .prf Γ (∀c[K] t, (∀[K] A) ~ (∀[K] B))
| apptc :
  Judgment .prf Γ (t1, (∀[K] A) ~ (∀[K] B)) ->
  Judgment .prf Γ (t2, C ~ D) ->
  Judgment .prf Γ (t1 `@c[ t2 ], (A β[C]) ~ (B β[D]))

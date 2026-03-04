import Surface.Typing
import Surface.Metatheory.Substitution
import Core.Metatheory.GlobalWf

namespace Surface


theorem EntryWf.from_lookup :
  ⊢s G ->
  lookup x G = some e ->
  EntryWf G e
:= by sorry
  -- intro wf h
  -- induction wf generalizing e
  -- case nil => simp [lookup] at h
  -- case cons G g gwf wf ih =>
  --   have gwf' := gwf
  --   have wf' := ListGlobalWf.cons gwf' wf
  --   cases gwf <;> simp [lookup] at h
  --   case data dx K ctors j1 _ j2 j3 =>
  --     split at h
  --     case _ e1 =>
  --       subst e1; injection h with e; subst e
  --       apply EntryWf.data; simp [lookup]
  --     case _ e1 =>
  --       replace h := Core.EntryWf.from_lookup_vec1 h
  --       rcases h with ⟨i, h⟩ | h
  --       case _ =>
  --         simp at h; obtain ⟨h1, h2⟩ := h
  --         rw [<-h2]
  --         generalize zdef : ctors i = z at *
  --         rcases z with ⟨z, zA⟩
  --         simp at *; subst h1
  --         obtain ⟨q1, q2, q3, q4⟩ := j2 i x zA zdef
  --         apply EntryWf.ctor dx K ctors; simp [lookup]
  --         exact zdef
  --         apply Kinding.global_weaken_ctors _ q1
  --         case _ =>
  --           intro x h
  --           unfold is_data at h
  --           simp [lookup_kind, lookup] at *
  --           split; simp [Entry.kind]
  --           split at h; case _ h1 h2 => exfalso; apply h1 h2
  --           rw [from_lookup_vec3]; intro i
  --           generalize wdef : ctors i = w
  --           cases w; case _ w wA =>
  --           simp; intro h; subst h
  --           obtain ⟨w1, w2, w3, w4⟩ := j2 i x wA wdef
  --           rw [w4] at h; simp [Option.isSome] at h
  --         exact q2; simp [lookup]
  --         split; case _ e => exfalso; apply e1 e
  --         case _ e =>
  --           rw [q4]
  --           apply from_lookup_vec2
  --           exists i; rw [zdef]; simp
  --           intro j w1 w2; apply j1 i j
  --           rw [<-w2, zdef]
  --       case _ => apply weaken wf' (ih h)
    -- case opent j1 j2 =>
    --   split at h
    --   case _ e1 =>
    --     subst e1; injection h with e; subst e
    --     apply EntryWf.opent j1; simp [lookup]
    --   case _ e1 => apply weaken wf' (ih h)
    -- case openm j1 j2 =>
    --   split at h
    --   case _ e1 =>
    --     subst e1; injection h with e; subst e
    --     apply EntryWf.openm
    --     apply Kinding.drop_weaken_global 1 wf' (by simp) j1
    --     simp [lookup]
    --   case _ e1 => apply weaken wf' (ih h)
    -- case defn j1 j2 j3 =>
    --   split at h
    --   case _ e1 =>
    --     subst e1; injection h with e; subst e
    --     apply EntryWf.defn
    --     apply Kinding.drop_weaken_global 1 wf' (by simp) j1
    --     apply Typing.drop_weaken_global 1 wf' (by simp) j2
    --     simp [lookup]
    --   case _ e1 => apply weaken wf' (ih h)
    -- case inst y T t j1 j2 =>
    --   replace ih := ih h
    --   apply weaken wf' ih
    -- case instty j1 j2 =>
    --   split at h
    --   case _ e1 =>
    --     subst e1; injection h with e; subst e
    --     apply EntryWf.instty
    --     apply ValidInstTy.drop_weaken_global 1 wf' (by simp) j1
    --     simp [lookup]
    --   case _ e1 => apply weaken wf' (ih h)

end Surface

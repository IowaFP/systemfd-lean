import Core.Metatheory.Erasure.Lemmas

namespace Core

-- theorem erasure_disjoint_index (wf : ⊢ G) (i j : Fin m): 
--   j ≠ i → ss j = ss' j
--   → ⟦ss j⟧ = ⟦ss' j⟧
--
-- Top to bottom: JUST question mark
-- Bottom to top should be star. Might be arbitrarily any steps at the top
-- TODO: explore bisimulations
theorem erasure (wf : ⊢ G) :
  G ⊢ t1 ~> t2 → ⟦G⟧ ⊢ ⟦t1⟧ ~>? ⟦t2⟧
-- TODO: determine why this broke!
| .beta (b := b) (t := t) => by
    simp
    rw[erasure_sub_tm_su b]
    exact .step .beta
| @Red.betat G t A b => by
  rw [erasure_subst_ty_su b t]
  simp
  -- TODO: show that 0 is free in b 
  -- (substitution has no var)
  -- See Apoorv lemma + erasure on substitution.
  -- Need to generalize to arbitrary number of typed lambdas AND patterns.
  -- Something similar to prove strengthening.
  -- Look at Core.Ty.FreeVars
  -- FV.var_not_in_one_more -> use this generalization
  --
  -- let h2 := Untyped.RedOpt.step (@Untyped.Red.beta ⟦G⟧ (λ⟦b⟧) .unit)
  -- simp at h2
  -- exact .step sorry
  sorry
| .cast => .refl
| .prj_fst_app | .prj_snd_app => .refl
| .prj_fst_arr | .prj_snd_arr => .refl
-- FIXME: with previous rules, this reduces to λλ#0 → λ#0.
-- *Is* adding a reduction here safe,
-- OR should erase just for .allc?
| .allc | .apptc => .refl
| @Red.defn G x A t hdf => .step (.defn (GlobalEnv.erasure_ty wf hdf))
| .ctor1_congr (v := .appt _) (t := t) (t' := t') s
| .app_congr (f := t) (f' := t') s => by
  simp
  generalize h1 : ⟦t⟧ = et
  generalize h2 : ⟦t'⟧ = et'
  have ih := erasure wf s
  rw[h1, h2] at ih
  rcases ih with _ | hr
  exact .refl
  exact .step (.app_congr hr)
| .ctor1_congr (v := .prj _) s => by apply erasure wf s
| .apptc_congr1 _ | .apptc_congr2 _ | .cast_congr _ => .refl
| .allc_congr s => by apply erasure wf s
-- Maybe prove: type variable doesn't show up anywhere (easier?)
--
-- | data_match {ss : Fun.Vec Term m} {ps : Fun.Vec (Pattern m) n} :
--   Term.IsData .cls ss.to ctors ->
--   Pattern.Match ctors (ps i) ->
--   b' = (bs i)[Constructor.subst_type ctors ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
--   Red G (.mtch m n ss ps bs) b'
-- | openm_match {i : Nat} {ss : Fun.Vec Term m} :
--   Term.IsData .opn ss.to ctors ->
--   G[i]? = some (.inst x p b) ->
--   Pattern.Match ctors p ->
--   b' = b[Constructor.subst_type ctors ++ Ts2.list.reverse.map su ++ Ts1.list.reverse.map su ++ Subst.id Ty][Constructor.subst ctors ++ Subst.id Term] ->
--   Red G (openm! x Ts1 Ts2 ss) b'
-- | openm_congr {ts : Fun.Vec Term n} i :
--   Red G (ts i) (ts' i) ->
--   (∀ j ≠ i, ts j = ts' j) ->
--   Red G (openm! x Ts1 Ts2 ts) (openm! x Ts1 Ts2 ts')
| @Red.match_congr G m ss' n ps bs ss i st a => by
    simp
    generalize hss' : ⟦ss' i⟧ = x'
    generalize hss : ⟦ss i⟧ = x
    let e := erasure wf st
    rw[hss', hss] at e
    cases e
    case _ =>
      have hfs : (fun n => ⟦ss n⟧) =  (fun n => ⟦ss' n⟧) := by grind
      rw[hfs]
      .exact .refl
    case _ st =>
      rw[←hss', ←hss] at st
      exact .step (@Untyped.Red.match_congr ⟦G⟧ m ⟦ss'⟧ n ⟦ps⟧ ⟦bs⟧ ⟦ss⟧ i st (erasure_match_cong a))
| _ => sorry


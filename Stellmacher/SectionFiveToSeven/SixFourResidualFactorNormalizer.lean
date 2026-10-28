module
public import Stellmacher.SectionFiveToSeven.SixFourSelectedModuleContainment
public import Stellmacher.SectionTwo.GlobalOffenderActionFactors
public import Theory.GroupAction.NormalizingActor

/-!
# Residual and Baumann normalization of the selected module in (6.4)

Under Hypothesis Two, suppose the canonical barred action has nontrivial
critical subgroup J. Every raw one-seven factor D has its original ambient
commutator module normalized by O²(P₁) join B(S).

The native P-family data and (5.3) provide the exact Section Two action
hypotheses. The offender-closure identity puts the quotient residual in E,
and the global Baumann action theorem puts the Baumann image in J ≤ E.
The direct product of all raw factors makes D normal in E. Its action
commutator is therefore invariant under the required quotient actors;
the named quotient conjugation formula transports that invariance into
the ambient group without changing the module or its action.

This is the residual-normalizer containment at the end of Stellmacher
(6.4), Journal of Algebra 190 (1997), p.32. Source:
`refs/files/stellmacher-n-group.pdf`; the abbreviated LaTeX transcription
omits the bars and several intermediate steps preserved by this module.
-/
namespace Stellmacher.SectionsFiveToSeven
universe u
public theorem sixFour_residual_factor_normalizer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) :
    letI := sectionSixQuotientAction h
    ∀ D : Subgroup (SectionSixBarP1 h),
      SectionOne.IsOneSevenFactor (V := sectionSixLocalV h) D →
      twoResidualAmbient P1 ⊔ baumannIn S ≤ Subgroup.normalizer
        (((commutatorAction D (sectionSixLocalV h)).map
          (P1.subtype.comp (sectionSixLocalV h).subtype) : Subgroup H) : Set H) := by
  classical
  let T := sectionSixSylow h
  let q := sectionSixQuotientMap h
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = SectionTwo.cSubgroup T := QuotientGroup.ker_mk' _
  let _ := sectionSixQuotientAction h
  have hsetup := sectionSix_barred_action_setup h
  have hTm : (T : Subgroup P1).map P1.subtype = S := hsetup.sylow_image
  obtain ⟨hsol, hchar, _⟩ := lemma_five_three S0 S P1 P2 h
  have hTne : (T : Subgroup P1) ≠ ⊥ := by
    intro ht
    apply h.fiveOne.S_nontrivial
    rw [← hTm, ht, Subgroup.map_bot]
  have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTne (Subgroup.card_eq_one.mp hc))
  have hsec : SectionTwo.Hypotheses P1 :=
    ⟨hsol, even_iff_two_dvd.mpr (hdvd.trans (T : Subgroup P1).card_subgroup_dvd_card), hchar⟩
  have hP := (pFamily_iff_pSet _ _ _).mp h.fiveOne.P1_mem
  have hcore : pCore 2 P1 ≠ ⊥ := by
    intro hc
    apply hP.1.2.2.1
    change (pCore 2 P1).map P1.subtype = ⊥
    rw [hc, Subgroup.map_bot]
  have hnot : (T : Subgroup P1) ≠ pCore 2 P1 := by
    intro hc
    apply hP.1.2.2.2
    rw [← hTm, hc]
    rfl
  have huniq : IsUniqueMaximalContaining (T : Subgroup P1) (⊤ : Subgroup P1) :=
    native_uniqueMaximalContaining P1 (T : Subgroup P1) (by rw [hTm]; exact hP.2)
  have hnative : (⊤ : Subgroup P1) ∈ SectionThree.PSet ⊤ (T : Subgroup P1) := by
    have hh := pFamily_range_of_injective (MonoidHom.id P1) Function.injective_id
      T (T : Subgroup P1) (Subgroup.map_id _) hcore hnot huniq
    rw [(MonoidHom.id P1).range_eq_top_of_surjective Function.surjective_id,
      pFamily_iff_pSet] at hh
    exact hh
  intro D hD
  let V := sectionSixLocalV h
  let X := SectionSixBarP1 h
  let _ : IsElementaryAbelian 2 V :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec T).2
  let U := T.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (U : Subgroup X)
  let E := SectionOne.oneE (V := V) (U : Subgroup X)
  have hJS : J ≤ (U : Subgroup X) := sSup_le fun _ ha => ha.1
  have hUne : (U : Subgroup X) ≠ ⊥ := fun hb => hJ (bot_unique (hb ▸ hJS))
  have hUd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hUne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable P1 := hsol
  have hOne : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (hUd.trans (U : Subgroup X).card_subgroup_dvd_card),
      SectionTwo.quotientConjugationAction_faithful T q hq hker,
      SectionTwo.lemma_two_one hsec T q hq hker⟩
  have hthree : SectionThree.Hypotheses P1 (T : Subgroup P1) :=
    ⟨hsec.even_order, hTne, T.isPGroup'⟩
  have hEeq := SectionThree.offender_normalClosure_eq_residual_sup T hthree hnative hsol
    q hq hOne hJ
  have hRmap : (twoResidualAmbient (⊤ : Subgroup P1)).map q =
      twoResidualAmbient (⊤ : Subgroup X) :=
    map_twoResidualAmbient_of_subgroup_image ⊤ q ⊤ (Subgroup.map_top_of_surjective q hq)
  have hRE : (twoResidualAmbient (⊤ : Subgroup P1)).map q ≤ E := by
    rw [hRmap]
    change _ ≤ SectionOne.oneE (V := V) ((T : Subgroup P1).map q)
    rw [hEeq]
    exact le_sup_left
  let B := (T : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup P1)) : Set P1)
  have hBm : B.map P1.subtype = baumannIn S := by
    dsimp [B]
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hTm]
    rfl
  have hBE : B.map q ≤ E :=
    (SectionTwo.global_offender_action_factors hsec T q hq hker B rfl hJ).1.trans
      Subgroup.le_normalClosure
  obtain ⟨_, hprod, _⟩ := SectionOne.oneSeven_global_product hOne U
  have hEid := (SectionOne.oneSeven_global_identification hOne U).2
  change E = SectionOne.oneSevenGenerated (G := X) (V := V) at hEid
  have hED : E ≤ Subgroup.normalizer (D : Set X) := by
    rw [hEid]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sSup hD)).mp
      (hprod.2.1 D ((SectionOne.mem_oneSevenFactors_iff D).mpr hD))
  let L := twoResidualAmbient (⊤ : Subgroup P1) ⊔ B
  have hLD : L.map q ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.map_sup]
    exact (sup_le hRE hBE).trans hED
  have hInv := commutatorAction_isInvariant_of_normalizing_actor (V := V) (L.map q) D hLD
  have hLm : L.map P1.subtype = twoResidualAmbient P1 ⊔ baumannIn S := by
    rw [Subgroup.map_sup, hBm]
    congr 1
    exact map_twoResidualAmbient_of_subgroup_image ⊤ P1.subtype P1 (by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
  rw [← hLm, Subgroup.le_normalizer_iff]
  intro l hl w hw
  obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hl
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  have hi := (hInv.invariant ⟨q l, Subgroup.mem_map_of_mem q hlL⟩ v).mp hv
  refine Subgroup.mem_map.mpr ⟨q l • v, hi, ?_⟩
  exact congrArg P1.subtype (SectionTwo.quotientConjugationAction_smul_coe T q hq hker l v)
end Stellmacher.SectionsFiveToSeven

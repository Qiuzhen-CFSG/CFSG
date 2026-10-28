module
public import Stellmacher.SectionFiveToSeven.SixFourBarredAction
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionFiveToSeven.PFamilyInjective
public import Stellmacher.SectionTwo.GlobalOffenderFixingFactor
public import Stellmacher.SectionTwo.GlobalOffenderActionFactors
public import Stellmacher.BaumannMap
public import Stellmacher.UniqueMaximalContainingTransport

/-!
# A fixing factor for the canonical barred action in (6.4)

Under Hypothesis Two, a vector in the original Section Six module that
centralizes the full preimage of nontrivial barred J but lies outside the
central involutions of S is fixed by a raw one-seven factor. The same
hypotheses put B(S) in its centralizer inside S.

The chosen intrinsic Sylow of P1 transports the local P-family predicate
and supplies the Section Two hypotheses from (5.3). The canonical setup
identifies ambient centralization with quotient fixed points. Since V is
elementary abelian and lies in the Sylow, a Sylow-fixed vector would lie
in its omega-center, giving the required nonfixedness. The original-module
factor-selection theorem then applies. Finally the global offender
decomposition puts the Baumann image in J, and the exact action formula
transports its fixedness back to ambient centralization.

This is the first paragraph on journal p.32 of Stellmacher (6.4), using
the barred setup on p.31. Source: `refs/files/stellmacher-n-group.pdf` and
the abbreviated `refs/latex/stellmacher-n-group.tex`. The action and its
canonical preimages are preserved throughout.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_canonical_fixing_factor
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : sectionSixBarredCritical h ≠ ⊥) (w : sectionSixLocalV h)
    (hwJ : ((w : P1) : H) ∈ Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H))
    (hwZ : ((w : P1) : H) ∉ omegaOneCenter S) :
    letI := sectionSixQuotientAction h
    baumannIn S ≤ S ⊓ Subgroup.centralizer ({((w : P1) : H)} : Set H) ∧
      ∃ D : Subgroup (SectionSixBarP1 h),
        SectionOne.IsOneSevenFactor (V := sectionSixLocalV h) D ∧
        w ∈ FixedPoints.subgroup D (sectionSixLocalV h) := by
  classical
  let T := sectionSixSylow h
  let V := sectionSixLocalV h
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
  let _ : IsElementaryAbelian 2 V := (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec T).2
  have hwfix : w ∈ FixedPoints.subgroup (sectionSixBarredCritical h) V :=
    (hsetup.mem_fixedPoints_iff w).mpr hwJ
  have hwS : w ∉ FixedPoints.subgroup ((T : Subgroup P1).map q) V := by
    intro hf
    apply hwZ
    apply (mem_omegaOneCenterAmbient_iff S _).mpr
    have hwT : (w : P1) ∈ (T : Subgroup P1) :=
      ((SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec T).1.trans
        ((pCore_isPGroup (p := 2) (G := P1)).le_sylow_of_normal T)) w.property
    refine ⟨hTm.le (Subgroup.mem_map_of_mem P1.subtype hwT), ?_, ?_⟩
    · exact congrArg P1.subtype
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) (w : P1) w.property)
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp (hTm.ge hs)
      have hf' : q t • w = w := hf ⟨q t, Subgroup.mem_map_of_mem q ht⟩
      have he := congrArg Subtype.val hf'
      rw [SectionTwo.quotientConjugationAction_smul_coe T q hq hker] at he
      exact congrArg P1.subtype (mul_inv_eq_iff_eq_mul.mp he)
  have hselected := SectionTwo.exists_global_offender_factor_fixing hsec T hnative q hq hker
    hJ w hwfix hwS
  let B := (T : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup P1)) : Set P1)
  have hBm : B.map P1.subtype = baumannIn S := by
    dsimp [B]
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hTm]
    rfl
  have hBJ := (SectionTwo.global_offender_action_factors hsec T q hq hker B rfl hJ).1
  refine ⟨le_inf inf_le_left ?_, hselected⟩
  intro b hb
  obtain ⟨b1, hb1, rfl⟩ := Subgroup.mem_map.mp (hBm.ge hb)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain rfl := hx
  have hbJ : q b1 ∈ sectionSixBarredCritical h := hBJ (Subgroup.mem_map_of_mem q hb1)
  have he : q b1 • w = w := hwfix ⟨q b1, hbJ⟩
  have he' := congrArg Subtype.val he
  rw [SectionTwo.quotientConjugationAction_smul_coe T q hq hker] at he'
  exact (congrArg P1.subtype (mul_inv_eq_iff_eq_mul.mp he')).symm

end Stellmacher.SectionsFiveToSeven

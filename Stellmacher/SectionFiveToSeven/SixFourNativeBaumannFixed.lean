module
public import Stellmacher.SectionFiveToSeven.SixFourBarredAction
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionFiveToSeven.PFamilyInjective
public import Stellmacher.UniqueMaximalContainingTransport
public import Stellmacher.SectionTwo.NativeBaumannGlobalOffender
public import Stellmacher.BaumannMap

/-!
# Native Baumann fixed vectors for the canonical barred (6.4) action

Under Hypothesis Two, suppose the native elementary Thompson subgroup of S
acts nontrivially on the actual Section Six module. Then the canonical
barred critical subgroup is nontrivial, and every vector centralized by
B(S) centralizes the entire canonical critical preimage.

The intrinsic Sylow in P₁ and its module retain the named canonical quotient
action. The local P-family and (5.3) give the genuine Section Two and P-set
hypotheses. Nontrivial native action descends to a nontrivial native Thompson
image. The local native/global identification makes the Baumann image exactly
the action-defined oneJ. Fixedness under that image then lifts through the
canonical fixed-vector equivalence, including the whole action kernel.

This is the exact bridge needed when Stellmacher applies (6.4) to native
Baumann central elements in (9.1) and (9.3), Journal of Algebra 190 (1997),
pp.47 and 50, `refs/files/stellmacher-n-group.pdf`. Nontrivial native action
is explicit; no unconditional equality of the two critical groups is used.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

public theorem sixFour_native_baumann_barred_fixed {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hJnative : ¬ elementaryAbelianMaxJ S ≤
      Subgroup.centralizer (sectionSixV S P1 : Set H)) :
    sectionSixBarredCritical h ≠ ⊥ ∧
      sectionSixV S P1 ⊓ Subgroup.centralizer (baumannIn S : Set H) ≤
        Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) := by
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
  let V := sectionSixLocalV h
  let J := elementaryAbelianMaxJ (T : Subgroup P1)
  let B := (T : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient J : Set P1)
  have hJmap : J.map P1.subtype = elementaryAbelianMaxJ S := by
    rw [← hTm]
    exact (elementaryAbelianMaxJ_map_injective P1.subtype P1.subtype_injective _).symm
  have hBmap : B.map P1.subtype = baumannIn S := by
    dsimp [B, J]
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hTm]
    rfl
  have hJne : J.map q ≠ ⊥ := by
    intro hj
    have hjker : J ≤ SectionTwo.cSubgroup T := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff J).mp hj
    apply hJnative
    rw [← hJmap]
    rintro j ⟨j1,hj1,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [← hsetup.localV_image] at hv
    obtain ⟨v1,hv1,rfl⟩ := hv
    exact congrArg P1.subtype (Subgroup.mem_centralizer_iff.mp (hjker hj1) v1 hv1)
  have hBbar := SectionTwo.native_baumann_image_eq_global_oneJ_of_pSet
    hsec T hnative q hq hker B rfl hJne
  change B.map q = sectionSixBarredCritical h at hBbar
  have hJB : J ≤ B := by
    refine le_inf (sSup_le fun A hA => hA.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨wJ, hwJ, rfl⟩ := hw
    obtain ⟨wZ, _, rfl⟩ := hwJ
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm
  refine ⟨?_,?_⟩
  · intro hj
    apply hJne
    exact bot_unique ((Subgroup.map_mono hJB).trans_eq (hBbar.trans hj))
  · intro w hw
    obtain ⟨v,hv,hveq⟩ := Subgroup.mem_map.mp (hsetup.localV_image.symm ▸ hw.1)
    let vector : V := ⟨v,hv⟩
    have he : ((vector : V) : H) = w := hveq
    rw [← he]
    apply (hsetup.mem_fixedPoints_iff vector).mp
    change vector ∈ FixedPoints.subgroup (sectionSixBarredCritical h) V
    rw [← hBbar]
    rw [FixedPoints.mem_subgroup]
    intro actor
    obtain ⟨b,hb,he⟩ := actor.property
    apply Subtype.ext
    change ((actor.val • vector : V) : P1) = v
    rw [← he,SectionTwo.quotientConjugationAction_smul_coe T q hq hker]
    apply P1.subtype_injective
    change (b : H) * (v : H) * (b : H)⁻¹ = (v : H)
    have hcomm := Subgroup.mem_centralizer_iff.mp hw.2 (b : H)
      (hBmap ▸ Subgroup.mem_map_of_mem P1.subtype hb)
    change (v : H) = w at hveq
    rw [hveq]
    exact mul_inv_eq_iff_eq_mul.mpr hcomm

end Stellmacher.SectionsFiveToSeven

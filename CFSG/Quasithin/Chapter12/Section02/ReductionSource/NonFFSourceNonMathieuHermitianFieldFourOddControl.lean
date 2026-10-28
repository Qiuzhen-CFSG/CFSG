module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOrdinaryExclusion
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCubicComparison

/-!
# Full odd-normalizer control for the original Hermitian nine-space

The actual odd-normalizer alternatives are a normal J₄ component or an
ordinary J₄ component from pushing up. The ordinary branch is already excluded.
For the normal branch, the full odd-actor comparison now includes prime three:
the exceptional cubic action is excluded by the original centralizer's inversion
on the residual cubic. Its full residual must therefore lie in N_G(L), contrary
to the proved Hermitian residual escape.

A characteristic elementary subgroup of every nontrivial abelian odd actor
then gives control of its whole ambient normalizer. This discharges the remaining
hypothesis of E.6.27 and proves r ≥ 4 on the unchanged original action, retaining
all covering kernels. The next module applies this bound to the zero weak-closure
configuration and assembles the complete tensor exclusion.
Source: Aschbacher–Smith 4.4.3 and Remark 4.4.2, E.6.27–28 and 7.4.1,
printed pp.619, 623, 257–258, 700, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem no_normal_janko_odd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {p : ℕ} (hp : p.Prime) (hop : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hc : HermitianNormalJankoCase L D.sourceOrbit A) : False := by
  obtain ⟨hu, K, hK, hn, hmove, hout, hcore, hVK, hFK, hcent, hr, ⟨e⟩, he⟩ := hc
  obtain ⟨z, hzV, hz, hTz, hRM⟩ :=
    D.sourceOrbit_hermitian_janko_odd_fixed_residual_comparison h.toHypothesis1221 hV
      hp hop A hne hAe
      (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer
        h.toHypothesis1221 hV))
      (by simpa only [hV] using hA.trans inf_le_right)
      K hK hn (by simpa only [hV] using hVK) hFK hout hcent e
  exact D.sourceOrbit_hermitian_normal_janko_residual_escape
    h hmany hV hnon d A K hVK hcent e z (by simpa only [hV] using hzV) hz hRM

/-- Every elementary odd actor fixing the original Hermitian nine-space
has its whole ambient normalizer in N_G(L), including prime three. -/
theorem sourceOrbit_hermitian_field_four_elementary_odd_normalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3, B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hop : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have ho : Odd (Nat.card A) := by
    obtain ⟨n, hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact hop.pow
  by_contra hout
  rcases D.sourceOrbit_hermitian_field_four_oddActor_janko_cases
    h hmany hV hnon d B eQ hfield A hne hA ho hout with hn | ho
  · exact D.no_normal_janko_odd h hmany hV hnon d hp hop A hne hAe hA hn
  · obtain ⟨J, H, W, hw, K, hK, _⟩ := ho
    exact D.sourceOrbit_hermitian_no_ordinary_janko h hmany hV hnon d B eQ hfield hw K hK

/-- Characteristic elementary reduction gives the full abelian odd-normalizer
control required by source E.6.27, on the unchanged original module. -/
theorem sourceOrbit_hermitian_field_four_abelian_odd_normalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3, B.Carrier))
    (hfield : B.degree = 2)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  obtain ⟨p, hp, E, _, hEchar, hEelem, hE⟩ :=
    (⊤ : Subgroup A).exists_elementaryAbelian_characteristic_le top_ne_bot
  let := hEchar
  let := hEelem
  let : Fact p.Prime := ⟨hp⟩
  have hoddE : Odd (Nat.card E) := ho.of_dvd_nat E.card_subgroup_dvd_card
  have hop : Odd p := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hn0
      have hcard := (one_lt_card_iff_ne_bot E).mpr hE
      rw [hn, hn0, pow_zero] at hcard
      omega
    exact hoddE.of_dvd_nat (hn.symm ▸ dvd_pow_self p hn0)
  have hEm : E.map A.subtype ≠ ⊥ := by
    intro hb
    exact hE ((E.map_eq_bot_iff_of_injective A.subtype_injective).mp hb)
  have hEn := D.sourceOrbit_hermitian_field_four_elementary_odd_normalizer_le
    h hmany hV hnon d B eQ hfield hp hop (E.map A.subtype) hEm
    (IsElementaryAbelian.map A.subtype) ((map_subtype_le E).trans hA)
  exact (normalizer_le_normalizer_characteristic_image A E).trans hEn

/-- The remaining field-four instance of source 7.4.1. All odd-normalizer
premises, including the cubic actor, are discharged on the original action. -/
theorem sourceOrbit_hermitian_field_four_globalR_ge_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3, B.Carrier))
    (hfield : B.degree = 2) : 4 ≤ globalR D.sourceOrbit := by
  apply D.sourceOrbit_hermitian_globalR_ge_four_mul_of_odd_control 1 d h hmany hV hnon
  intro A hne hA ho hcomm
  let := hcomm
  exact D.sourceOrbit_hermitian_field_four_abelian_odd_normalizer_le
    h hmany hV hnon d B eQ hfield A hne hA ho

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

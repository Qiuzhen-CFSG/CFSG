module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.NormalTwoThreeLayer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The dihedral obstruction for a normal source component

In the single-component E.2.2 row, the literal source kernel lies in
K O₂(X). A two-closed covered Borel in the {2,3}-maximal subgroup is
absorbed by that subgroup's two-three core. Thus a dihedral quotient of
order eight forces eight to divide the index of KJ. In the actual core-free
star quotient, K has nonabelian simple image and trivial centralizer, so
this index divides the order of the component's outer automorphism group.

This retains the original maximal subgroup, normal core and component;
no splitting or identification of a central cover with its simple quotient
is assumed. Source: Aschbacher--Smith E.2.2 and 10.2.3(3), printed
pp.215--216,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall
open scoped Pointwise

private theorem threeGroup_of_six_and_odd {Y : Type*} [Group Y] [Finite Y]
    (hY : IsPGroup 6 Y) (ho : Odd (Nat.card Y)) : IsPGroup 3 Y := by
  obtain ⟨n,hn⟩ := hY.exists_card_dvd_pow
  apply IsPGroup.of_card_dvd_pow (n := n)
  have hc : Nat.Coprime (Nat.card Y) (2 ^ n) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr ho.not_two_dvd_nat).symm.pow_right n
  apply hc.dvd_of_dvd_mul_left
  simpa only [show (6 : ℕ) = 2 * 3 from rfl, mul_pow] using hn

/-- The original covered Borel lies in the maximal subgroup’s two-three core. -/
theorem overlap_le_twoThreeCore {X : Type*} [Group X] [Finite X]
    {M K : Subgroup X} [K.Normal]
    (hM : IsPGroup 6 M) (hi : Odd (pCore 2 (K.subgroupOf M)).index) :
    K.subgroupOf M ≤ (pCore 3 (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M)) := by
  apply le_twoThreeCore_of_normal
  apply threeGroup_of_six_and_odd
  · exact (hM.to_subgroup (K.subgroupOf M)).of_surjective
      (QuotientGroup.mk' (pCore 2 (K.subgroupOf M))) (QuotientGroup.mk'_surjective _)
  · simpa only [index_eq_card] using hi

/-- The actual dihedral overlap quotient forces an order-eight outer divisor. -/
theorem normal_dihedral_outer_divisor {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬ Group.IsSolvable X) (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hM : IsPGroup 6 (minimalParabolicMax S hP))
    (hi : Odd (pCore 2 (K.subgroupOf (minimalParabolicMax S hP))).index)
    (hd : Nonempty (((minimalParabolicMax S hP) ⧸
      (pCore 3 ((minimalParabolicMax S hP) ⧸ pCore 2 (minimalParabolicMax S hP))).comap
        (QuotientGroup.mk' (pCore 2 (minimalParabolicMax S hP)))) ≃* DihedralGroup 4)) :
    8 ∣ Nat.card (MulAut.Outer (sourceImage (minimalParabolicMax S hP) K)) := by
  let M := minimalParabolicMax S hP
  let J := minimalParabolicCore S hP
  let O := pCore 2 X
  let q := QuotientGroup.mk' J
  let A := K.map q
  let R := (pCore 3 (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M))
  have hKR : K.subgroupOf M ≤ R := overlap_le_twoThreeCore hM hi
  have hOM : O ≤ M := (pCore_isPGroup.le_sylow_of_normal S).trans (minimalParabolicMax_spec S hP).2
  have hOR : O.subgroupOf M ≤ R := by
    have ht : IsPGroup 2 (O.subgroupOf M) := pCore_isPGroup.comap_subtype
    have ho : O.subgroupOf M ≤ pCore 2 M := le_sSup ⟨inferInstance,ht⟩
    exact ho.trans (by
      intro x hx
      change QuotientGroup.mk' (pCore 2 M) x ∈ pCore 3 (M ⧸ pCore 2 M)
      have he : QuotientGroup.mk' (pCore 2 M) x = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 M) x).mpr hx
      rw [he]
      exact one_mem _)
  have hJO : J ≤ K ⊔ O := by
    have hj : J.map (QuotientGroup.mk' O) ≤ K.map (QuotientGroup.mk' O) := by
      change (sourceKernel M).map (QuotientGroup.mk' O) ≤ actorImage K
      rw [hc.kernel_center]
      exact map_subtype_le _
    simpa only [comap_map_eq,QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hj
  have hNR : (K ⊔ J).subgroupOf M ≤ R := by
    intro x hx
    have hx' : x.val ∈ K ⊔ O := (sup_le le_sup_left hJO) hx
    obtain ⟨k,hk,o,ho,he⟩ := mem_sup_of_normal_left.mp hx'
    have hkm : k ∈ M := by
      have hh := M.mul_mem x.property (M.inv_mem (hOM ho))
      rw [← he, mul_inv_cancel_right] at hh
      exact hh
    have hh := R.mul_mem (hKR (show (⟨k,hkm⟩ : M) ∈ K.subgroupOf M from hk))
      (hOR (show (⟨o,hOM ho⟩ : M) ∈ O.subgroupOf M from ho))
    have hxe : (⟨k,hkm⟩ : M) * ⟨o,hOM ho⟩ = x := Subtype.ext he
    rwa [hxe] at hh
  obtain ⟨e⟩ := hd
  have hdvd : 8 ∣ (K ⊔ J).index := by
    have hr : R.index = 8 := by
      rw [index_eq_card, Nat.card_congr e.toEquiv]
      simp [DihedralGroup.card]
    have h := (index_dvd_of_le hNR).trans ((K ⊔ J).relIndex_dvd_index_of_normal (K := M))
    rwa [hr] at h
  have hia := Structure.source_normal_simple_image S hP hs K hK hgen
  let : IsSimpleGroup A := hia.1
  have ha : ¬ IsMulCommutative A := hia.2.1
  have hR : K = pResidual 2 X := SingleClauses.component_eq_residual hc hK
  have hAR : A = pResidual 2 (X ⧸ J) := by
    dsimp [A]
    rw [hR,map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective J)]
  have hquot : IsPGroup 2 ((X ⧸ J) ⧸ A) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hAR).symm
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  have hstar := Structure.source_star_minimal_core_free S hP
  have hcore : pCore 2 (X ⧸ J) = ⊥ := by
    apply le_bot_iff.mp
    have ht := twoCore_le_sourceKernel Sq hstar.1
    change pCore 2 (X ⧸ J) ≤ minimalParabolicCore Sq hstar.1 at ht
    exact ht.trans hstar.2.le
  have hcent := centralizer_eq_bot_of_simple_two_quotient A ha hquot hcore
  have haidx : A.index = (K ⊔ J).index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective J),index_top,mul_one]
  have hout : Nat.card ((X ⧸ J) ⧸ A) ∣ Nat.card (MulAut.Outer A) :=
    card_dvd_of_injective (MulAut.outerAction A) (MulAut.outerAction_injective A hcent)
  exact (hdvd.trans (by rw [← haidx]; rfl)).trans hout

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

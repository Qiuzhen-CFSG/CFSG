module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalModel
public import Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Intrinsic core control from the source parabolic normalizer

Inside the four-block stabilizer of order 1152, a subgroup with order
divisible by 576 has index at most two and is normal. Consequently every
two-subgroup normalized by it and contained in it lies in the intrinsic
two-core of the full stabilizer. This lets the source use its Sylow order
and cubic rank, without assuming a parabolic identification.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117, and B.3.2(6).
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear.OrthogonalModel
open Theory.SpecificGroups.SymmetricEight
open A6ShadowTwoLocals

/-- Order divisibility forces relative normality in the full point stabilizer. -/
theorem normal_of_large_fourBlock_subgroup (J : Subgroup S8)
    (hJ : J ≤ fourStabilizer) (hc : 576 ∣ Nat.card J) :
    (J.subgroupOf fourStabilizer).Normal := by
  let L := J.subgroupOf fourStabilizer
  have h := L.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hJ).toEquiv,
    FourBlockSylowResidual.fourStabilizer_card] at h
  have hcard : 576 ≤ Nat.card J := Nat.le_of_dvd Nat.card_pos hc
  have hi : L.index = 1 ∨ L.index = 2 := by
    have hp : 0 < L.index := Nat.pos_of_ne_zero L.index_ne_zero_of_finite
    have hb : L.index ≤ 2 := by nlinarith
    omega
  rcases hi with hi | hi
  · have ht : L = ⊤ := index_eq_one.mp hi
    change L.Normal
    rw [ht]
    infer_instance
  · exact normal_of_index_eq_two hi

/-- The two-core is controlled by the actual large normalizer, rather than
by an unconnected abstract name for the parabolic. -/
theorem le_fourBlockCore_of_large_normalizer (J B : Subgroup S8)
    (hJ : J ≤ fourStabilizer) (hc : 576 ∣ Nat.card J)
    (hBJ : B ≤ J) (hB : IsPGroup 2 B)
    (hn : J ≤ normalizer (B : Set S8)) : B ≤ fourStabilizer.pCoreIn 2 := by
  have hnormal := normal_of_large_fourBlock_subgroup J hJ hc
  have hnJ : fourStabilizer ≤ normalizer (J : Set S8) :=
    (normal_subgroupOf_iff_le_normalizer hJ).mp hnormal
  exact (le_pCoreIn_of_normalizes hB hBJ hn).trans
    (pCoreIn_mono_of_normalizes hJ hnJ)

/-- B.3.2(6) now applies with only the literal normalizer, Sylow/cubic order,
and two-group inputs left to the original source consumer. -/
theorem not_offender_of_large_normalizer (J B A : Subgroup S8)
    (hJ : J ≤ fourStabilizer) (hc : 576 ∣ Nat.card J)
    (hBJ : B ≤ J) (hB : IsPGroup 2 B)
    (hn : J ≤ normalizer (B : Set S8)) (hAB : A ≤ B) :
    ¬ IsOffender (BinaryPermutation.naturalRepresentation (Fin 8)) A :=
  not_isOffender_of_le_fourBlockCore A
    (hAB.trans (le_fourBlockCore_of_large_normalizer J B hJ hc hBJ hB hn))

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear.OrthogonalModel

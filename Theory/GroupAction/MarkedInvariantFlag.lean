module

public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Marked vectors in an invariant binary flag

An automorphism of a finite elementary binary group with at most two fixed
points fixes the generator of an invariant line. On an invariant plane
containing that line, it sends any vector outside the line to its product
with the line generator. The line also makes the fixed-point bound exact.

The proof enumerates the two elements of the line and the four elements
of the plane. This is the marked-coordinate step in Parrott's matrix
calculation, *A characterization of the Tits' simple group* (1972),
printed pp.674 and 677–678.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupAction

/-- An invariant line and plane determine the first two marked coordinates
of an automorphism with at most two fixed points. -/
public theorem marked_invariant_flag
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (b : MulAut W) (t v : W) (ht : t ≠ 1) (hv : v ≠ 1) (hvt : v ≠ t)
    (hline : b t ∈ zpowers t) (hplane : b v ∈ zpowers t ⊔ zpowers v)
    (hbound : Nat.card (FixedPoints.subgroup (zpowers b) W) ≤ 2) :
    b t = t ∧ b v * v = t ∧
      Nat.card (FixedPoints.subgroup (zpowers b) W) = 2 := by
  classical
  have hs (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hot : orderOf t = 2 := orderOf_eq_prime (by simpa only [pow_two] using hs t) ht
  have hbt : b t = t := by
    rw [mem_zpowers_iff_mem_range_orderOf, hot] at hline
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hline
    have hi2 := Finset.mem_range.mp hi
    interval_cases i
    · exact (ht (b.injective (by simpa using heq.symm))).elim
    · simpa using heq.symm
  have hle : zpowers t ≤ FixedPoints.subgroup (zpowers b) W := by
    apply zpowers_le.mpr
    exact (MulAut.mem_fixed_zpowers_iff b t).mpr hbt
  have hcard : Nat.card (FixedPoints.subgroup (zpowers b) W) = 2 := by
    have hh := card_le_of_le hle
    rw [Nat.card_zpowers, hot] at hh
    omega
  have hmove : b v ≠ v := by
    intro heq
    obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff'
      (1 : FixedPoints.subgroup (zpowers b) W)).mp hcard
    have hvF := (MulAut.mem_fixed_zpowers_iff b v).mpr heq
    have htF := (MulAut.mem_fixed_zpowers_iff b t).mpr hbt
    apply hvt
    exact congrArg Subtype.val ((huniq ⟨v, hvF⟩ (by
      intro hh; exact hv (congrArg Subtype.val hh))).trans
      (huniq ⟨t, htF⟩ (by intro hh; exact ht (congrArg Subtype.val hh))).symm)
  have hclosure : zpowers t ⊔ zpowers v = closure ({t, v} : Set W) := by
    rw [show ({t, v} : Set W) = {t} ∪ {v} by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union],
      closure_union]
    simp only [← zpowers_eq_closure]
  rw [hclosure, mem_closure_pair_iff t v (hs t) (hs v) (Commute.all t v)] at hplane
  refine ⟨hbt, ?_, hcard⟩
  rcases hplane with hh | hh | hh | hh
  · exact (hv (b.injective (hh.trans (map_one b).symm))).elim
  · exact (hvt (b.injective (hh.trans hbt.symm))).elim
  · exact (hmove hh).elim
  · rw [hh, mul_assoc, hs, mul_one]

end Theory.GroupAction

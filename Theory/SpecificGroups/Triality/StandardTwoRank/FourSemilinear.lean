module

public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.RankCriterion
public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.HighestRoot
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.SpecificGroups.Triality.BinaryCenter

/-!+# Automorphism two-rank at the field of order four

The intrinsic two-rank is ten and the outer group is cyclic. Every elementary
automorphism group preserves some Sylow two-subgroup. An inner kernel of
rank ten must contain the central elementary highest-root subgroup, because
adjoining it cannot increase the intrinsic rank. The semilinear highest-root
calculation rules out pointwise fixation by a noninner involution. Thus an
elementary automorphism group with nontrivial outer image has inner kernel
of rank at most nine and total rank at most ten.

Simplicity and perfectness are inherited from the source component on this
same genuine carrier. There are no normalization or fixed-descent premises.
Source: Aschbacher--Smith G.9.3, printed p.356 (`refs/quasithin.pdf`),
and GLS3 §§2.3--2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.TwoRank.FourSemilinear
open Parabolics RadicalCoordinates.Centers OuterOdd

private theorem highestRoot_elementary :
    IsElementaryAbelian 2 (highestRoot (binaryParameters 2 (Nat.succ_pos 1))) := by
  let P := binaryParameters 2 (Nat.succ_pos 1)
  let e := highestRootEquiv P rfl
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply e.symm.injective
    simp only [map_mul, mul_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    change 2 • (e.symm x).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _

/-- The sufficient sharp automorphism bound for the genuine group ³D₄(4). -/
theorem automorphism_twoRank_le_ten
    [IsSimpleGroup (BinaryCarrier 2 (Nat.succ_pos 1))]
    [Group.IsPerfect (BinaryCarrier 2 (Nat.succ_pos 1))] :
    primeRank 2 (MulAut (BinaryCarrier 2 (Nat.succ_pos 1))) ≤ 10 := by
  let P := binaryParameters 2 (Nat.succ_pos 1)
  let : IsCyclic (MulAut.Outer (BinaryCarrier 2 (Nat.succ_pos 1))) :=
    outer_isCyclic_of_inner_coefficient P (Coverage.binary_inner_coefficient 2 (Nat.succ_pos 1))
  let : IsElementaryAbelian 2 (highestRoot P) := highestRoot_elementary
  apply automorphism_twoRank_le_of_moved_central
    (binaryCarrier_center_eq_bot 2 (Nat.succ_pos 1))
    (twoRank_le_five_mul 2 (Nat.succ_pos 1)) (unipotentSylow P rfl) (highestRoot P)
  · intro z hz u hu
    obtain ⟨w, hw, rfl⟩ := highestRoot_le_center_unipotent P rfl hz
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hw) ⟨u, hu⟩)).symm
  · exact noninner_involution_not_fix_highestRoot

end Triality.Standard.TwoRank.FourSemilinear

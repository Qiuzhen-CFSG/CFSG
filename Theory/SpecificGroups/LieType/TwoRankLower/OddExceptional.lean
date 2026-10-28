module
public import Theory.GroupTheory.IndependentInvolutionsRank
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E6
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E7
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E8
/-!
# Odd-characteristic two-rank in the actual E6, E7 and E8 carriers

The existing faithful four-root chart has commuting coroot involutions
which independently invert its coordinates. Their projective images
therefore contain an elementary eight. This uses only the original root
words, with no new representation, order or classification hypothesis.
Source: GLS3 §2.6; Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace ExceptionalSplit.OddRankFour
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
namespace SixNodes
variable (c : SixNodes b) (F : Type*) [Field F]
theorem detector_square (i : Fin 4) : c.detector F i ^ 2 = 1 := by
  fin_cases i
  · exact ((c.coroot_commute F 1 3).mul_pow 2).trans (by rw [coroot_square,coroot_square,mul_one])
  · exact ((c.coroot_commute F 4 3).mul_pow 2).trans (by rw [coroot_square,coroot_square,mul_one])
  · exact c.coroot_square F 3
  · exact c.coroot_square F 2

theorem detector_commute (i j : Fin 4) : Commute (c.detector F i) (c.detector F j) := by
  let C := Subgroup.closure (Set.range (c.coroot F))
  have hm (k : Fin 6) : c.coroot F k ∈ C := Subgroup.subset_closure ⟨k,rfl⟩
  have hd (k : Fin 4) : c.detector F k ∈ C := by
    fin_cases k
    · exact C.mul_mem (hm 1) (hm 3)
    · exact C.mul_mem (hm 4) (hm 3)
    · exact hm 3
    · exact hm 2
  let : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro x ⟨k,rfl⟩ y ⟨l,rfl⟩
    exact c.coroot_commute F k l)
  let : CommGroup C := IsMulCommutative.instCommGroup
  exact congrArg Subtype.val (mul_comm (⟨c.detector F i,hd i⟩:C) (⟨c.detector F j,hd j⟩:C))

variable [Finite F] [P.IsIrreducible]
include c in
theorem three_le_twoRank (h2 : (2 : F) ≠ 0) : 3 ≤ primeRank 2 (Model P b F) := by
  let d : Fin 4 → Model P b F := fun i => projection P b F (c.detector F i)
  refine IndependentInvolutions.three_le_of_coordinate_actors
    (c.projectiveChart F) (c.projectiveChart_injective F h2) (Multiplicative.ofAdd (1:F))
    ?_ d ?_ ?_ ?_ (fun i : Fin 3 => i.castLE (by decide)) ?_
  · intro h
    have he : (-1:F)=1 := congrArg Multiplicative.toAdd h
    apply h2
    have : (1:F)+1=0 := neg_eq_iff_add_eq_zero.mp he
    simpa only [one_add_one_eq_two] using this
  · intro i
    change (projection P b F (c.detector F i)) ^ 2 = 1
    rw [← map_pow, detector_square, map_one]
  · intro i j
    exact (c.detector_commute F i j).map (projection P b F)
  · intro i a
    change projection P b F (c.detector F i) * projection P b F (c.chart F a) *
      (projection P b F (c.detector F i))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, detector_chart]
    rfl
  · intro i j h
    exact Fin.ext (congrArg (fun k : Fin 4 => k.val) h)
end SixNodes
end ExceptionalSplit.OddRankFour

namespace Theory.SpecificGroups.LieType.TwoRank
open Theory.AlgebraicGroup.StandardRootSystem
open ExceptionalSplit.OddRankFour
local instance oddE6RootsFintype : Fintype typeE6Roots := Fintype.ofFinite _
local instance oddE7RootsFintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance oddE8RootsFintype : Fintype typeE8Roots := Fintype.ofFinite _
local instance oddE6Irreducible : typeE6RootPairing.IsIrreducible := TwistedE6.TheoremDRootNormalizer.pairing_irreducible
variable (F : Type*) [Field F] [Finite F]

/-- The actual odd-characteristic E6 carrier contains an elementary eight. -/
theorem odd_e6_three_le (h2 : (2 : F) ≠ 0) :
    3 ≤ primeRank 2 (ExceptionalSplit.E6 F) := E6.nodes.three_le_twoRank F h2

/-- The actual odd-characteristic E7 carrier contains an elementary eight. -/
theorem odd_e7_three_le (h2 : (2 : F) ≠ 0) :
    3 ≤ primeRank 2 (ExceptionalSplit.E7 F) := E7.nodes.three_le_twoRank F h2

/-- The actual odd-characteristic E8 carrier contains an elementary eight. -/
theorem odd_e8_three_le (h2 : (2 : F) ≠ 0) :
    3 ≤ primeRank 2 (ExceptionalSplit.E8 F) := E8.nodes.three_le_twoRank F h2

end Theory.SpecificGroups.LieType.TwoRank

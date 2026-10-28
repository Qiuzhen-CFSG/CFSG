module

public import Theory.SpecificGroups.SU3.FourAutomorphismBound
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# The full automorphism group of PSU₃(4) is nine-free

Transport to the standard Hermitian form preserves the actual outer group.
Its order divides four, and the group itself has order 62400. Consequently
the full automorphism order divides 249600, which has only one factor three.
Source: Aschbacher--Smith 14.3.20, printed p.998, the unitary row.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F]

/-- Arbitrary stored Hermitian forms give the same nine-free automorphism order. -/
theorem four_not_nine_dvd_card_aut (J : HermitianForm 3 F)
    (hcard : Nat.card F = 4 ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 4) :
    ¬ 9 ∣ Nat.card (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 4 hcard hfixed
  have ho : Nat.card (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) ∣ 4 := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact FourAutomorphismBound.outer_card_dvd_four (FormTransport.standardForm J) rfl hcard hfixed
  have hg : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 62400 := by
    rw [Representation.SU3.BinaryDegree.card_projective J hcard hfixed]
    norm_num
  have hi : Nat.card (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ∣ 62400 :=
    hg ▸ card_range_dvd (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _)
  have hd : Nat.card (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∣ 249600 := by
    rw [← (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)).card_mul_index]
    exact Nat.mul_dvd_mul hi ho
  exact fun h => (by decide : ¬ 9 ∣ 249600) (h.trans hd)

end BenderSuzuki.MatrixGroups.HermitianForm

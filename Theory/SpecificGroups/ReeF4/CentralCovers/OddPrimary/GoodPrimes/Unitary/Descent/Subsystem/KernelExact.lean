module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ScalarKernel
/-!
# The exact diagonal cubic kernel

The scalar coordinates of the two A₂ factors cancel precisely on the diagonal:
their remaining torus entries are inverse cubes, and the determinant-one
condition makes each cube one. Together with the injectivity and centralizer
argument in `ScalarKernel`, this identifies the complete kernel, including
its converse, on the original full SL₃ factors.
Source: GLS3 §2.6.2 and Example 2.6.3.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

theorem pairMap_central_diagonal (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot)
    (A : SL3 F) (hA : A ∈ center (SL3 F)) : pairMap L S hL hS (A,A) = 1 := by
  obtain ⟨a, ha, he⟩ := central_coroot_expression A hA
  have ha3 : a ^ 3 = 1 := by
    apply Units.ext
    have hd := A.property
    rw [ha] at hd
    simpa [Matrix.scalar, Matrix.det_diagonal] using hd
  change L A * S A = 1
  rw [he, map_mul, map_mul, markedMap_coroot hL, markedMap_coroot hL,
    markedMap_coroot hS, markedMap_coroot hS]
  simp only [Three.Descent.ExceptionalTorus.coroot_diagonal, ← map_mul]
  rw [← map_one Cyclotomic.diagonal]
  congr 1
  funext i
  fin_cases i <;>
    simp [longRoot, shortRoot, Three.Descent.ExceptionalTorus.lowestRoot_corootCoordinates,
      corootCoordinates_simple, ha3]
  · rw [← _root_.mul_inv_rev, ← pow_succ, ha3, inv_one]
  · rw [← _root_.mul_inv_rev, ← pow_succ', ha3, inv_one]


/-- Equality in the actual F₄ image detects exactly the diagonal cubic center. -/
theorem pairMap_kernel_iff (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot)
    (hLi : Function.Injective L) (hSi : Function.Injective S) (A B : SL3 F) :
    pairMap L S hL hS (A,B) = 1 ↔ A = B ∧ A ∈ center (SL3 F) := by
  constructor
  · exact pairMap_kernel L S hL hS hLi hSi A B
  · rintro ⟨rfl, hA⟩
    exact pairMap_central_diagonal L S hL hS A hA

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem

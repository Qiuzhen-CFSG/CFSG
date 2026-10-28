module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.Seeds

/-!
# Ten concrete candidates for the outside-kernel involution fibers

For e₀,...,e₁₀ the certified binary kernel basis, write E(m) for the
product selected by the bits of m. The candidates are x*E(0), x*E(16),
and (xy)^7*E(m) for m=28,50,70,104,138,164,208,254.
They arise by solving the binary square-one equation over the two proposed
quotient involution representatives. Coverage and ambient fusion of this
finite list are separate proof obligations, not assertions here.

The ATLAS local generators and binary basis are documented in
`Cardinality.Subgroup` and `LocalOrder.KernelCount.BinarySpan`.
-/

@[expose] public section
namespace Janko4.Simplicity.Max1Fusion
open Cardinality Cardinality.KernelCount

/-- Fixed binary masks specifying the ten outside-kernel candidate words. -/
def outsideMask : Fin 10 → ℕ := ![0, 16, 28, 50, 70, 104, 138, 164, 208, 254]

/-- Actual local subgroup elements, independently of any coverage assertion. -/
def outsideRepresentative (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (i : Fin 10) : max1Subgroup hA hB :=
  (if i.val < 2 then localX hA hB else (localX hA hB * localY hA hB) ^ 7) *
    binaryProduct (basis hA hB) (fun j => (outsideMask i).testBit j.val)

/-- Entry zero is the first local generator and already fuses to `a`. -/
theorem outsideRepresentative_zero_fuses
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Fuses hA hB (outsideRepresentative hA hB 0 : Model) := by
  have he : outsideRepresentative hA hB 0 = localX hA hB := by
    simp [outsideRepresentative, outsideMask, binaryProduct_zero]
  rw [he]
  obtain ⟨g, hg⟩ := localX_fuses_first hA hB
  exact ⟨g, Or.inl hg⟩

end Janko4.Simplicity.Max1Fusion

module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PairMatrices
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# Matrix witnesses for generation by the fixed G₂(3) pair

A matrix witness records an element of the closure of the literal pair whose
faithful coordinate matrix is the given matrix. Small product and inverse
certificates preserve this property; faithfulness transfers it to a specified
octonion automorphism. Long words therefore need only small arithmetic checks.

Adapted from `G2Five/AtlasOctonionGenerationCertificate.lean`. The root, Weyl
and torus formulas are the ATLAS port: see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. Discovery words are in `../source/`.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.Generation

/-- Closure of the fixed pair, using exactly the comparison map's marking. -/
def pairClosure : Subgroup (Model (ZMod 3)) :=
  Subgroup.closure (Set.range generator)

/-- The nontrivial unit of the prime field. -/
def twoUnit : (ZMod 3)ˣ := Units.mk0 2 (by decide)

/-- A matrix realized by some element of the closure of the fixed pair. -/
def MatrixInClosure (M : Mat) : Prop :=
  ∃ g ∈ pairClosure, coordinateMatrix g = M

theorem matrixInClosure_a : MatrixInClosure matrixA :=
  ⟨generator false, Subgroup.subset_closure ⟨false, rfl⟩, coordinateMatrix_false⟩

theorem matrixInClosure_b : MatrixInClosure matrixB :=
  ⟨generator true, Subgroup.subset_closure ⟨true, rfl⟩, coordinateMatrix_true⟩

theorem matrixInClosure_mul {M N P : Mat} (hM : MatrixInClosure M)
    (hN : MatrixInClosure N) (hP : ProductEntries M N P) : MatrixInClosure P := by
  obtain ⟨g, hg, hgm⟩ := hM
  obtain ⟨h, hh, hhn⟩ := hN
  exact ⟨g * h, pairClosure.mul_mem hg hh, mul_certificate hgm hhn hP⟩

theorem matrixInClosure_inv {M N : Mat} (hM : MatrixInClosure M)
    (hN : ProductEntries M N 1) : MatrixInClosure N := by
  obtain ⟨g, hg, hgm⟩ := hM
  exact ⟨g⁻¹, pairClosure.inv_mem hg, inv_certificate hgm hN⟩

theorem mem_of_matrixInClosure {g : Model (ZMod 3)} {M : Mat}
    (hM : MatrixInClosure M) (hg : coordinateMatrix g = M) : g ∈ pairClosure := by
  obtain ⟨h, hh, he⟩ := hM
  have : g = h := coordinateMatrix_injective (hg.trans he.symm)
  simpa only [this] using hh

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.Generation

module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Intertwiners
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Checks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Reduction

/-!
# Irreducibility of the literal binary J₄ module

For `X = 1 + A + B + AB + B²`, exact packed certificates bound its kernel
by a line whose generator has full cyclic span. A left-kernel vector also
has full cyclic span. If a stable subspace contains the first vector, it
is the whole module. Otherwise `X` is injective, hence surjective, on that
finite subspace. The second vector then annihilates it, and dual cyclicity
forces the subspace to be zero.

This proves irreducibility over `ZMod 2` of the actual ATLAS matrices,
the part of GLS3 Table 5.3i's Small Representation clause needed by the
fixed-generator intertwiner argument. The source clause also asserts
absolute irreducibility; that stronger assertion is not used here.
See `Model/Data.lean` for attribution and the precise row convention.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator
open Matrix IrreducibilityCertificate

/-- Every binary subspace stable under the two literal ATLAS generators
is zero or the whole 112-dimensional space. -/
theorem generatorIrreducible : GeneratorIrreducible := by
  apply irreducible_of_cyclic_kernel (decodeRows testRows) (decodeRows eliminationRows)
    (vector rightSeed) (vector leftSeed) (Pi.single (111 : Fin 112) 1)
    reconstruction left_annihilates
  · intro W hA hB v hv
    rw [testRows_correct, add_mulVec, add_mulVec, add_mulVec, add_mulVec,
      one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    exact W.add_mem
      (W.add_mem (W.add_mem (W.add_mem hv (hA v hv)) (hB v hv)) (hA _ (hB v hv)))
      (hB _ (hB v hv))
  · intro W hA hB hr
    apply eq_top_of_rows W columnOrbit columnInverse column_inverse
    apply orbit_mem W columnOrbit columnParents transposeA transposeB column_steps
    · intro v hv
      rw [transposeA_correct, vecMul_transpose]
      exact hA v hv
    · intro v hv
      rw [transposeB_correct, vecMul_transpose]
      exact hB v hv
    · simpa only [column_seed] using hr
  · intro W hA hB hl
    apply eq_top_of_rows W rowOrbit rowInverse row_inverse
    apply orbit_mem W rowOrbit rowParents aRows bRows row_steps hA hB
    simpa only [row_seed] using hl

end Janko4.OuterReduction.FixedGenerator

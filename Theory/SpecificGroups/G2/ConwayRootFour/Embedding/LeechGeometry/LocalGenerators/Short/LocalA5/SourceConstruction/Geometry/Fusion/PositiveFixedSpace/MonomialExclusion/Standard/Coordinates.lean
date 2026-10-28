module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Lattice
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Sextet

/-!
# Signed Golay matrices on the literal binary Leech quotient

The explicit integral coordinates identify the simultaneous binary fixed space
of two monomial Leech isometries with the common kernel of their displayed
matrices minus the identity. This is the coordinate bridge needed by the
standard-sextet calculation in Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284. In particular no ambient coordinate reduction replaces Λ/2Λ.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators Matrix
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.StandardCoordinates

/-- A fully explicit matrix for the literal signed-coordinate action. -/
def monomialMatrix (a : GolayMonomialGroup) : Matrix (Fin 24) (Fin 24) Bit :=
  fun i j => ((∑ k : Fin 24, dualMatrix i k *
    (if a.left.toAdd.val (flat.symm k) = 0 then
      basisMatrix (flat (monomialPull a (flat.symm k))) j else
      -basisMatrix (flat (monomialPull a (flat.symm k))) j)) / 8 : ℤ)

theorem monomialMatrix_eq (a : GolayMonomialGroup) :
    monomialMatrix a = actionMatrix (monomialEmbedding a) := by
  ext i j
  change ((_ / 8 : ℤ) : Bit) = ((integerDot (dualRow i)
    ((monomialEmbedding a).val (basisVector j)).val / 8 : ℤ) : Bit)
  congr 2

/-- Coordinates of the simultaneous fixed space, for the actual consumer. -/
def commonKernel (a m : GolayMonomialGroup) : Submodule Bit (Fin 24 → Bit) :=
  LinearMap.ker (Matrix.mulVecLin (monomialMatrix a) - LinearMap.id) ⊓
    LinearMap.ker (Matrix.mulVecLin (monomialMatrix m) - LinearMap.id)

theorem binaryCoordinates_mem_kernel (a : GolayMonomialGroup) (v : LeechModTwo) :
    binaryCoordinates v ∈ LinearMap.ker (Matrix.mulVecLin (monomialMatrix a) - LinearMap.id) ↔
      v ∈ binaryFixed (monomialEmbedding a) := by
  change monomialMatrix a *ᵥ binaryCoordinates v - binaryCoordinates v = 0 ↔
    leechModTwoRepresentation (monomialEmbedding a) v - v = 0
  rw [monomialMatrix_eq, ← binaryCoordinates_action, ← map_sub]
  exact binaryCoordinates.map_eq_zero_iff

def commonKernelEquiv (a m : GolayMonomialGroup) :
    ↥(binaryFixed (monomialEmbedding a) ⊓ binaryFixed (monomialEmbedding m)) ≃ₗ[Bit]
      commonKernel a m where
  toFun v := ⟨binaryCoordinates v.val,
    (binaryCoordinates_mem_kernel a _).mpr v.property.1,
    (binaryCoordinates_mem_kernel m _).mpr v.property.2⟩
  invFun v := ⟨binaryCoordinates.symm v.val, by
    have h := v.property
    rw [← binaryCoordinates.apply_symm_apply v.val] at h
    exact ⟨(binaryCoordinates_mem_kernel a _).mp h.1,
      (binaryCoordinates_mem_kernel m _).mp h.2⟩⟩
  left_inv v := by apply Subtype.ext; exact binaryCoordinates.symm_apply_apply _
  right_inv v := by apply Subtype.ext; exact binaryCoordinates.apply_symm_apply _
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c v := by apply Subtype.ext; exact map_smul _ _ _

theorem commonFixed_finrank (a m : GolayMonomialGroup) :
    Module.finrank Bit ↥(binaryFixed (monomialEmbedding a) ⊓ binaryFixed (monomialEmbedding m)) =
      Module.finrank Bit (commonKernel a m) := (commonKernelEquiv a m).finrank_eq

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.StandardCoordinates

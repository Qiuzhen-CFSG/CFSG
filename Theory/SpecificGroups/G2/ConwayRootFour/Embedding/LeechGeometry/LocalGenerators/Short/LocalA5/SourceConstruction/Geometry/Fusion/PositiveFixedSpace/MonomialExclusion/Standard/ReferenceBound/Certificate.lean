module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Data

/-!
# Checking eight common fixed vectors in the literal Leech coordinates

An eight-column matrix fixed by both actions, with a matrix left inverse,
embeds the binary eight-space in their common kernel. This certificate proves
linear independence without enumerating the 256 linear combinations. The final
bridge substitutes the actual signed-coordinate matrices into this argument.

Source context: the reference calculation for Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284. Candidate coverage and the finite certificates
are separate obligations; the lattice-coordinate comparison is already proved.
-/

open Atlas.Codes Atlas.Lattices
open scoped Matrix
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

theorem rawMatrix_eq_monomialMatrix (m : GolayMonomialGroup) :
    rawMatrix (fun i => m.left.toAdd.val (StandardCoordinates.flat.symm i))
      (fun i => StandardCoordinates.flat (monomialPull m (StandardCoordinates.flat.symm i))) =
    StandardCoordinates.monomialMatrix m := rfl

theorem referenceMatrix_eq (a b : GolayMonomialGroup) (h : ReferenceQuaternionPair a b) :
    StandardCoordinates.monomialMatrix a = referenceMatrix := by
  unfold StandardCoordinates.monomialMatrix referenceMatrix rawMatrix
  simp only [h.1, h.2.2.1]
  rfl

theorem candidateMatrix_eq (m : GolayMonomialGroup) (r : Fin 512)
    (h : CandidateMatches m r) :
    StandardCoordinates.monomialMatrix m = candidateMatrix r := by
  unfold StandardCoordinates.monomialMatrix candidateMatrix rawMatrix
  simp only [h.1, h.2]
  rfl

/-- All three identities are finite equations over `Bit`. -/
structure EightFrame (A M : Matrix (Fin 24) (Fin 24) Bit) where
  vectors : Matrix (Fin 24) (Fin 8) Bit
  retract : Matrix (Fin 8) (Fin 24) Bit
  fixed_left : A * vectors = vectors
  fixed_right : M * vectors = vectors
  independent : retract * vectors = 1

/-- The arithmetic obligation is independent of coverage of the candidate table. -/
def CandidateFrames : Prop :=
  ∀ r : Fin 512, Nonempty (EightFrame referenceMatrix (candidateMatrix r))

theorem eight_le_finrank_matrixKernel (A M : Matrix (Fin 24) (Fin 24) Bit) (V : Matrix (Fin 24) (Fin 8) Bit)
    (L : Matrix (Fin 8) (Fin 24) Bit)
    (hA : A * V = V) (hM : M * V = V) (hL : L * V = 1) :
    8 ≤ Module.finrank Bit ↥(LinearMap.ker (Matrix.mulVecLin A - LinearMap.id) ⊓
      LinearMap.ker (Matrix.mulVecLin M - LinearMap.id)) := by
  let K := LinearMap.ker (Matrix.mulVecLin A - LinearMap.id) ⊓
      LinearMap.ker (Matrix.mulVecLin M - LinearMap.id)
  have hv (x : Fin 8 → Bit) : V *ᵥ x ∈ K := by
    constructor
    · change A *ᵥ (V *ᵥ x) - V *ᵥ x = 0
      rw [Matrix.mulVec_mulVec, hA, sub_self]
    · change M *ᵥ (V *ᵥ x) - V *ᵥ x = 0
      rw [Matrix.mulVec_mulVec, hM, sub_self]
  let f : (Fin 8 → Bit) →ₗ[Bit] K := (Matrix.mulVecLin V).codRestrict K hv
  have hi : Function.Injective f := by
    intro x y h
    have he : V *ᵥ x = V *ᵥ y := congrArg Subtype.val h
    have hl := congrArg (fun z => L *ᵥ z) he
    simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using hl
  simpa using LinearMap.finrank_le_finrank_of_injective hi

/-- Application of a checked frame to the exact common kernel in the task. -/
theorem commonKernel_bound_of_frame (a b m : GolayMonomialGroup) (r : Fin 512)
    (hp : ReferenceQuaternionPair a b) (hm : CandidateMatches m r)
    (hf : EightFrame referenceMatrix (candidateMatrix r)) :
    8 ≤ Module.finrank Bit (StandardCoordinates.commonKernel a m) := by
  unfold StandardCoordinates.commonKernel
  rw [referenceMatrix_eq a b hp, candidateMatrix_eq m r hm]
  exact eight_le_finrank_matrixKernel _ _ hf.vectors hf.retract
    hf.fixed_left hf.fixed_right hf.independent

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

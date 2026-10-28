module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Certificate
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.ReferenceMatrix

/-!
# A checked nonidentity reference-centralizer certificate

Candidate 32 swaps two pairs of tetrads and has zero sign. Its displayed eight
vectors are fixed by both literal quotient matrices, and the selected coordinate
rows give a left inverse. The final theorem applies this certificate to any
actual monomial with these parameters.

This representative measures the calculation before extending it to the whole
candidate family. It does not prove coverage or the other 511 certificates.
Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes Atlas.Lattices
open scoped Matrix
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

def candidate32Rows : Fin 24 → ℕ := ![1,2,4,8,16,32,64,128,65536,66388,66872,983324,69918,3342614,5701966,7072187,256,196948,327992,461168,1114398,1253724,1458236,15427997]

def candidate32Table : Matrix (Fin 24) (Fin 24) Bit := fun i => maskBit (candidate32Rows i)

def candidate32Vectors : Matrix (Fin 24) (Fin 8) Bit :=
  ![![0,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,0],![0,1,0,0,0,0,0,0],![1,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,0],![1,1,0,0,0,0,0,0],![0,1,0,0,0,0,0,0],![1,0,0,0,0,0,0,0],![0,0,1,0,0,0,0,0],![1,0,1,0,0,0,0,0],![0,1,1,0,0,0,0,0],![0,0,0,1,0,0,0,0],![1,1,1,1,0,0,0,0],![0,0,0,0,1,0,0,0],![0,0,0,0,0,1,0,0],![0,0,1,1,1,1,0,0],![0,0,1,0,0,0,0,0],![1,0,1,0,0,0,0,0],![0,1,1,0,0,0,0,0],![0,1,0,1,0,0,0,0],![0,0,0,0,0,0,1,0],![0,1,1,0,1,0,1,0],![1,0,0,0,0,1,1,0],![0,0,0,0,0,0,0,1]]

def candidate32Pivots : Fin 8 → Fin 24 := ![1,2,8,11,13,14,20,23]

def candidate32Retract : Matrix (Fin 8) (Fin 24) Bit := fun i j => if candidate32Pivots i = j then 1 else 0

def candidate32Pull : Fin 24 → Fin 24 := ![0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15]

set_option Elab.async false in
theorem candidate32_sign : candidateSign 32 = (fun _ => 0) := by decide +kernel

set_option Elab.async false in
theorem candidate32_pull : candidatePull 32 = candidate32Pull := by decide +kernel

set_option Elab.async false in
theorem candidate32_matrix : candidateMatrix 32 = candidate32Table := by
  unfold candidateMatrix
  rw [candidate32_sign, candidate32_pull]
  decide +kernel

set_option Elab.async false in
theorem candidate32_fixed_reference : referenceTable * candidate32Vectors = candidate32Vectors := by decide +kernel

set_option Elab.async false in
theorem candidate32_fixed_self : candidate32Table * candidate32Vectors = candidate32Vectors := by decide +kernel

set_option Elab.async false in
theorem candidate32_independent : candidate32Retract * candidate32Vectors = 1 := by decide +kernel

set_option Elab.async false in
theorem candidate32_frame : Nonempty (EightFrame referenceMatrix (candidateMatrix 32)) := by
  refine ⟨⟨candidate32Vectors, candidate32Retract, ?_, ?_, candidate32_independent⟩⟩
  · rw [referenceMatrix_table]; exact candidate32_fixed_reference
  · rw [candidate32_matrix]; exact candidate32_fixed_self

/-- Actual common-kernel application of the representative certificate. -/
theorem commonKernel_bound_of_candidate32 (a b m : GolayMonomialGroup)
    (hp : ReferenceQuaternionPair a b) (hm : CandidateMatches m 32) :
    8 ≤ Module.finrank Bit (StandardCoordinates.commonKernel a m) := by
  obtain ⟨frame⟩ := candidate32_frame
  exact commonKernel_bound_of_frame a b m 32 hp hm frame

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

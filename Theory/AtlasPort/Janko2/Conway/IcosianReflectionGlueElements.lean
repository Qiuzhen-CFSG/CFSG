/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionGlueElements.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionGlueImage

/-!
# IcosianReflectionGlueElements

Verified monomial reflection words give elements of the finite glue image. Unipotent
parameter addition supplies the relations used for generation.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionGlueElements.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

theorem icosianReflectionGlueImage_mem_of_word (g : IcosianUnitMonomial)
    (hg : icosianMonomialReduction g∈icosianGlueMonomialStabilizer GoldenFour)
    (f : icosianHermitianGroup) (hf : f∈icosianReflectionGroup)
    (he : f.val=icosianMonomialRepresentation g) :
    icosianMonomialReduction g∈icosianReflectionGlueImage := by
  let a : icosianLiftedMonomial := ⟨g,hg⟩
  have ha : icosianMonomialToHermitian a=f := Subtype.ext he.symm
  refine ⟨a,?_,rfl⟩
  change icosianMonomialToHermitian a∈icosianReflectionGroup
  rw [ha]
  exact hf

theorem icosianMonomial_mem_of_representation (g : IcosianUnitMonomial)
    (f : icosianHermitianGroup) (he : f.val=icosianMonomialRepresentation g) :
    icosianMonomialReduction g∈icosianGlueMonomialStabilizer GoldenFour := by
  rw [← icosianMatrixGlue_stabilizes_iff]
  intro A
  choose x hx using fun i => icosianModuloTwo_surjective (A i)
  have hxA : (fun i => icosianModuloTwo (x i))=A := funext hx
  have h := f.property.2.2 (Atlas.Lattices.icosianCoordinateEmbedding x)
  rw [he] at h
  change Atlas.Lattices.icosianCoordinateEmbedding x∈Atlas.Lattices.rationalIcosianLattice ↔
    Atlas.Lattices.icosianCoordinateEmbedding (icosianMonomialIntegral g x)
      ∈Atlas.Lattices.rationalIcosianLattice at h
  rw [icosianCoordinateEmbedding_mem_iff,icosianCoordinateEmbedding_mem_iff,
    Atlas.Lattices.icosianLeechModule_matrix_glue,Atlas.Lattices.icosianLeechModule_matrix_glue,
    icosianMonomialIntegral_reduction,hxA] at h
  exact h.symm

theorem icosianReflectionGlueImage_mem_of_actual_word (g : IcosianUnitMonomial)
    (f : icosianHermitianGroup) (hf : f∈icosianReflectionGroup)
    (he : f.val=icosianMonomialRepresentation g) :
    icosianMonomialReduction g∈icosianReflectionGlueImage :=
  icosianReflectionGlueImage_mem_of_word g (icosianMonomial_mem_of_representation g f he) f hf he

def icosianGlueUnipotent (a b : GoldenFour) : IcosianGlueMonomialGroup GoldenFour :=
  SemidirectProduct.inl (icosianGlueBlockParameter 1 a b)

theorem icosianGlueUnipotent_mul (a b c d : GoldenFour) :
    icosianGlueUnipotent a b*icosianGlueUnipotent c d=
      icosianGlueUnipotent (a+c) (b+d) := by
  unfold icosianGlueUnipotent
  rw [← map_mul,icosianGlueBlockParameter_unipotent_mul]

theorem icosianGlueUnipotent_mem (a b : GoldenFour) :
    icosianGlueUnipotent a b∈icosianGlueMonomialStabilizer GoldenFour := by
  rw [icosianGlueMonomialStabilizer_iff]
  exact (icosianGlueBlockParameterElement (1,a,b)).property

end Atlas.Conway

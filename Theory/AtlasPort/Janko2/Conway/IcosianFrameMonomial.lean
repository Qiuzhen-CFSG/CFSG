/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianFrameMonomial.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianFrameCoordinates
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialFaithfulness

/-!
# IcosianFrameMonomial

The recovered coefficients express every frame stabilizer element as an integral unit
monomial map. Lattice preservation forces its reduction to preserve the glue.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianFrameMonomial.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Pointwise BigOperators
attribute [local irreducible] icosianFramePermutation icosianFrameCoefficient
attribute [local irreducible] icosianGlueMonomialStabilizer icosianNormOneReduction

def icosianFrameUnit (f : icosianCoordinateFrameStabilizer) (i : Fin 3) :
    icosianNormOneGroup := icosianNormOneGroupOf (icosianFrameCoefficient f i)
      (icosianFrameCoefficient_integral f i) (icosianFrameCoefficient_norm f i)

def icosianFrameMonomial (f : icosianCoordinateFrameStabilizer) : IcosianUnitMonomial :=
  ⟨fun i => icosianFrameUnit f ((icosianFramePermutation f).symm i),icosianFramePermutation f⟩

theorem icosianHermitian_single (f : icosianHermitianGroup) (i : Fin 3)
    (a : IcosianQuaternion) :
    f.val (Pi.single i a)=icosianRightMul (f.val (Pi.single i 1)) a := by
  rw [← f.property.1]
  congr 1
  funext j
  by_cases hj : j=i <;> simp [icosianRightMul,hj]

theorem icosianFrameMonomial_apply (f : icosianCoordinateFrameStabilizer)
    (x : IcosianRationalCoordinates) (j : Fin 3) :
    icosianMonomialRepresentation (icosianFrameMonomial f) x j=
      icosianFrameCoefficient f ((icosianFramePermutation f).symm j)*
        x ((icosianFramePermutation f).symm j) := rfl

theorem icosianFrameMonomial_representation (f : icosianCoordinateFrameStabilizer) :
    icosianMonomialRepresentation (icosianFrameMonomial f)=f.val.val := by
  have haxis (i : Fin 3) :
      icosianMonomialRepresentation (icosianFrameMonomial f) (Pi.single i 1)=
        f.val.val (Pi.single i 1) := by
    rw [icosianFrameCoefficient_spec]
    funext j
    rw [icosianFrameMonomial_apply]
    by_cases hj : j=icosianFramePermutation f i
    · subst j
      simp
    · have hj' : (icosianFramePermutation f).symm j≠i := by
        intro h; apply hj; simpa using congrArg (icosianFramePermutation f) h
      simp [hj,hj']
  apply LinearEquiv.ext
  intro x
  have hx : x=icosianRightMul (Pi.single 0 1) (x 0)+
      icosianRightMul (Pi.single 1 1) (x 1)+
      icosianRightMul (Pi.single 2 1) (x 2) := by
    funext i; fin_cases i <;> simp [icosianRightMul]
  rw [hx]
  simp only [map_add,icosianMonomialRepresentation_right_linear,f.val.property.1,haxis]

theorem icosianCoordinateEmbedding_mem_iff (x : IcosianCoordinates) :
    icosianCoordinateEmbedding x∈rationalIcosianLattice ↔ x∈icosianLeechModule := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hxy : y=x := by
      funext i
      apply Subtype.ext
      exact congrFun he i
    simpa [hxy] using hy
  · intro hx; exact ⟨x,hx,rfl⟩

theorem icosianFrameMonomial_mem (f : icosianCoordinateFrameStabilizer) :
    icosianFrameMonomial f∈icosianLiftedMonomial := by
  change icosianMonomialReduction (icosianFrameMonomial f)∈icosianGlueMonomialStabilizer GoldenFour
  rw [← icosianMatrixGlue_stabilizes_iff]
  intro A
  choose x hx using fun i => icosianModuloTwo_surjective (A i)
  have he : (fun i => icosianModuloTwo (x i))=A := funext hx
  have h := f.val.property.2.2 (icosianCoordinateEmbedding x)
  rw [← icosianFrameMonomial_representation f] at h
  change icosianCoordinateEmbedding x∈rationalIcosianLattice ↔
    icosianCoordinateEmbedding (icosianMonomialIntegral (icosianFrameMonomial f) x)
      ∈rationalIcosianLattice at h
  rw [icosianCoordinateEmbedding_mem_iff,icosianCoordinateEmbedding_mem_iff,
    icosianLeechModule_matrix_glue,icosianLeechModule_matrix_glue,
    icosianMonomialIntegral_reduction,he] at h
  exact h.symm

end Atlas.Conway

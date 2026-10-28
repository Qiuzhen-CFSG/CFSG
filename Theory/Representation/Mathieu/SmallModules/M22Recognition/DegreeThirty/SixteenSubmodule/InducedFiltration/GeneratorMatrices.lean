module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.Section
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Sparse matrix assembly for the induced binary adjoint

An explicit right-coset section gives one nonzero 16-by-16 block in each of
22 block rows. This module proves that local binary matrices for the 44 actual
stabilizer corrections assemble into generator matrices for the literal induced
adjoint, with a genuine linear and representation equivalence.

The general assembly lemmas retain arbitrary local coordinates as parameters.
Their concrete application uses `LocalBlocks.coordinates` and the certified
executable blocks, discharging every local premise. The matrices `A` and `B`
therefore act on 352 binary coordinates for the literal induction. `E` is the
linear equivalence from the published coset model, and `inducedBinaryEquiv`
is the full representation equivalence from the central-cover induction.

Each matrix entry is computed by the inverse generator permutation and one
explicit sixteen-dimensional conjugation block over the quadratic field. The
native marking comparison is part of the coordinate equivalence. The final
subrepresentation constructor turns stability under these two matrices into
invariance under the entire native M22 action. No factor filtration or
simplicity assertion is made here.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16, and
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices

/-- The 352 binary coordinates, arranged in 22 blocks of size 16. -/
abbrev BinaryCoordinates := (Fin 22 × Fin 16) → ZMod 2

/-- Apply one fixed fiber equivalence at all 22 points. -/
noncomputable def pointCoordinates (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    PointAdjoint ≃ₗ[ZMod 2] BinaryCoordinates where
  toFun v p := e (v p.1) p.2
  invFun w i := e.symm (fun j => w (i, j))
  left_inv v := by funext i; exact e.symm_apply_apply (v i)
  right_inv w := by
    funext p
    change e (e.symm (fun j => w (p.1, j))) p.2 = w p
    rw [e.apply_symm_apply]
  map_add' v w := by funext p; simp
  map_smul' c v := by funext p; simp

/-- Transport the literal section action to binary coordinates. -/
noncomputable def coordinateRep (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Representation (ZMod 2) M22 BinaryCoordinates :=
  (pointCoordinates e).conjRingEquiv.toMonoidHom.comp sectionAdjoint

/-- The fiber coordinate change as a representation equivalence. -/
noncomputable def sectionCoordinateEquiv (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Representation.Equiv sectionAdjoint (coordinateRep e) where
  toLinearEquiv := pointCoordinates e
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change pointCoordinates e (sectionAdjoint g v) =
      pointCoordinates e (sectionAdjoint g ((pointCoordinates e).symm (pointCoordinates e v)))
    rw [(pointCoordinates e).symm_apply_apply]

/-- Binary coordinates for the published coset representation. -/
noncomputable def cosetCoordinateEquiv (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Representation.Equiv cosetAdjoint (coordinateRep e) :=
  cosetSectionEquiv.trans (sectionCoordinateEquiv e)

/-- Binary coordinates for the literal induced adjoint representation. -/
noncomputable def inducedCoordinateEquiv (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Representation.Equiv inducedAdjoint (coordinateRep e) :=
  inducedCosetEquiv.trans (cosetCoordinateEquiv e)

/-- An executable sparse rule, once the 22 local blocks are supplied. -/
def sparseMatrix (k : Fin 2) (blocks : Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2)) :
    Matrix (Fin 22 × Fin 16) (Fin 22 × Fin 16) (ZMod 2) :=
  fun p q => if q.1 = generatorPoint k p.1 then blocks p.1 p.2 q.2 else 0

theorem sparseMatrix_mulVec (k : Fin 2)
    (blocks : Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (v : BinaryCoordinates) (i : Fin 22) (j : Fin 16) :
    (sparseMatrix k blocks).mulVec v (i, j) =
      (blocks i).mulVec (fun l => v (generatorPoint k i, l)) j := by
  simp [Matrix.mulVec, dotProduct, sparseMatrix, Fintype.sum_prod_type, ite_mul]

/-- Local correction matrices give the full generator action. -/
theorem coordinateRep_generator (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (k : Fin 2) (blocks : Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hb : ∀ i v, e (pointAdjoint (generatorCorrection k i) v) = (blocks i).mulVec (e v))
    (w : BinaryCoordinates) :
    coordinateRep e (generator k) w = (sparseMatrix k blocks).mulVec w := by
  funext p
  rcases p with ⟨i, j⟩
  change e (sectionAdjoint (generator k) ((pointCoordinates e).symm w) i) j = _
  rw [sectionAdjoint_generator, hb, sparseMatrix_mulVec]
  change (blocks i).mulVec (e (e.symm (fun l => w (generatorPoint k i, l)))) j = _
  rw [e.apply_symm_apply]

/-- Apply local correction certificates to the actual coset action. -/
theorem cosetCoordinateEquiv_generator (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (k : Fin 2) (blocks : Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hb : ∀ i v, e (pointAdjoint (generatorCorrection k i) v) = (blocks i).mulVec (e v))
    (v : CosetAdjoint) :
    cosetCoordinateEquiv e (cosetAdjoint (generator k) v) =
      (sparseMatrix k blocks).mulVec (cosetCoordinateEquiv e v) := by
  have h := LinearMap.congr_fun ((cosetCoordinateEquiv e).isIntertwining' (generator k)) v
  change cosetCoordinateEquiv e (cosetAdjoint (generator k) v) =
    coordinateRep e (generator k) (cosetCoordinateEquiv e v) at h
  rw [h, coordinateRep_generator e k blocks hb]

/-- Apply local correction certificates to the literal central-cover induction. -/
theorem inducedCoordinateEquiv_generator (e : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (k : Fin 2) (blocks : Fin 22 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hb : ∀ i v, e (pointAdjoint (generatorCorrection k i) v) = (blocks i).mulVec (e v))
    (v : InducedAdjoint) :
    inducedCoordinateEquiv e (inducedAdjoint (generator k) v) =
      (sparseMatrix k blocks).mulVec (inducedCoordinateEquiv e v) := by
  have h := LinearMap.congr_fun ((inducedCoordinateEquiv e).isIntertwining' (generator k)) v
  change inducedCoordinateEquiv e (inducedAdjoint (generator k) v) =
    coordinateRep e (generator k) (inducedCoordinateEquiv e v) at h
  rw [h, coordinateRep_generator e k blocks hb]

/-- The two executable 352-by-352 generator matrices, stored by a sparse block rule. -/
def generatorMatrix (k : Fin 2) :
    Matrix (Fin 22 × Fin 16) (Fin 22 × Fin 16) (ZMod 2) :=
  sparseMatrix k (LocalBlocks.blocks k)

/-- The binary matrix of the native ATLAS generator A. -/
def A : Matrix (Fin 22 × Fin 16) (Fin 22 × Fin 16) (ZMod 2) := generatorMatrix 0

/-- The binary matrix of the native ATLAS generator B. -/
def B : Matrix (Fin 22 × Fin 16) (Fin 22 × Fin 16) (ZMod 2) := generatorMatrix 1

/-- Sparse multiplication reads exactly one source block for each output point. -/
theorem generatorMatrix_mulVec (k : Fin 2) (v : BinaryCoordinates)
    (i : Fin 22) (j : Fin 16) :
    (generatorMatrix k).mulVec v (i, j) =
      (LocalBlocks.blocks k i).mulVec (fun l => v (generatorPoint k i, l)) j :=
  sparseMatrix_mulVec k (LocalBlocks.blocks k) v i j

/-- The native induced action in the explicit binary coordinates. -/
noncomputable def binaryAdjoint : Representation (ZMod 2) M22 BinaryCoordinates :=
  coordinateRep LocalBlocks.coordinates

/-- The actual representation equivalence from the published right-coset model. -/
noncomputable def cosetBinaryEquiv : Representation.Equiv cosetAdjoint binaryAdjoint :=
  cosetCoordinateEquiv LocalBlocks.coordinates

/-- The actual representation equivalence from the literal central-cover induction. -/
noncomputable def inducedBinaryEquiv : Representation.Equiv inducedAdjoint binaryAdjoint :=
  inducedCoordinateEquiv LocalBlocks.coordinates

/-- The requested linear coordinates on the published coset carrier. -/
noncomputable def E : CosetAdjoint ≃ₗ[ZMod 2] BinaryCoordinates :=
  cosetBinaryEquiv.toLinearEquiv

/-- Both generator identities, with all local correction premises discharged. -/
theorem binaryAdjoint_generator (k : Fin 2) (v : BinaryCoordinates) :
    binaryAdjoint (generator k) v = (generatorMatrix k).mulVec v :=
  coordinateRep_generator LocalBlocks.coordinates k (LocalBlocks.blocks k)
    (LocalBlocks.correction_blocks k) v

theorem E_generator (k : Fin 2) (v : CosetAdjoint) :
    E (cosetAdjoint (generator k) v) = (generatorMatrix k).mulVec (E v) :=
  cosetCoordinateEquiv_generator LocalBlocks.coordinates k (LocalBlocks.blocks k)
    (LocalBlocks.correction_blocks k) v

theorem E_generatorA (v : CosetAdjoint) :
    E (cosetAdjoint m22GeneratorAInM22 v) = A.mulVec (E v) :=
  E_generator 0 v

theorem E_generatorB (v : CosetAdjoint) :
    E (cosetAdjoint m22GeneratorBInM22 v) = B.mulVec (E v) :=
  E_generator 1 v

/-- Generator matrices for the literal induced representation, without extra premises. -/
theorem inducedBinaryEquiv_generator (k : Fin 2) (v : InducedAdjoint) :
    inducedBinaryEquiv (inducedAdjoint (generator k) v) =
      (generatorMatrix k).mulVec (inducedBinaryEquiv v) :=
  inducedCoordinateEquiv_generator LocalBlocks.coordinates k (LocalBlocks.blocks k)
    (LocalBlocks.correction_blocks k) v

theorem inducedBinaryEquiv_generatorA (v : InducedAdjoint) :
    inducedBinaryEquiv (inducedAdjoint m22GeneratorAInM22 v) =
      A.mulVec (inducedBinaryEquiv v) :=
  inducedBinaryEquiv_generator 0 v

theorem inducedBinaryEquiv_generatorB (v : InducedAdjoint) :
    inducedBinaryEquiv (inducedAdjoint m22GeneratorBInM22 v) =
      B.mulVec (inducedBinaryEquiv v) :=
  inducedBinaryEquiv_generator 1 v

/-- The coordinate carrier has the required binary dimension. -/
theorem finrank_binaryCoordinates : Module.finrank (ZMod 2) BinaryCoordinates = 352 := by
  simp [BinaryCoordinates]

/-- Stability under the two numerical matrices is invariance under native M22. -/
theorem binaryAdjoint_mem_of_generator_matrices (W : Submodule (ZMod 2) BinaryCoordinates)
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (hB : ∀ v ∈ W, B.mulVec v ∈ W)
    (g : M22) : ∀ v ∈ W, binaryAdjoint g v ∈ W := by
  have hg : g ∈ Subgroup.closure
      ({m22GeneratorAInM22, m22GeneratorBInM22} : Set M22) := by
    rw [m22_generators_closure_eq_top]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · simpa only [← generator_zero, binaryAdjoint_generator, A] using hA
    · simpa only [← generator_one, binaryAdjoint_generator, B] using hB
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : W → W := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective binaryAdjoint g).1 (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : binaryAdjoint g w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv)

/-- A numerical subspace certificate gives an actual subrepresentation.
The parent filtration construction can use its literal subspace and quotient. -/
noncomputable def subrepresentationOfMatrices (W : Submodule (ZMod 2) BinaryCoordinates)
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (hB : ∀ v ∈ W, B.mulVec v ∈ W) :
    Subrepresentation binaryAdjoint where
  toSubmodule := W
  apply_mem_toSubmodule g _ hv := binaryAdjoint_mem_of_generator_matrices W hA hB g _ hv

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices

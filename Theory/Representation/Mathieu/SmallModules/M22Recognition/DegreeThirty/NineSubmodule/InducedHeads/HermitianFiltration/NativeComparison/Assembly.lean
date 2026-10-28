module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.Flag
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.Section
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.Marking

/-!
# Native Hermitian generator comparison from finite block certificates

The proved section change replaces chosen right-coset representatives with the
explicit native transversal. One binary equivalence in the Hermitian fiber then
gives 22 blocks of size nine, with the exact inverse-generator source index.
A checked rectangular change of basis compares these matrices with either saved
GAP orientation and supplies the actual flag consumer.

This is a conditional assembly, not the unconditional generator comparison.
The missing inputs are executable Hermitian correction blocks and their checked
similarity with the saved matrices. Neither dimensions nor a GAP isomorphism
assertion supplies these inputs. The shared correction-lift producer constructs
the native pair/SL identities consumed by `correction_blocks_of_pair_lifts`.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452,457.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
namespace NativeComparison

open SixteenSubmodule.GeneratorMatrices

abbrev BinaryIndex := Fin 22 × Fin 9
abbrev BinarySpace := BinaryIndex → ZMod 2

/-- Apply the same binary fiber coordinates at each point of the native action. -/
def pointCoordinates (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2)) :
    PointSpace ≃ₗ[ZMod 2] BinarySpace where
  toFun v p := e (v p.1) p.2
  invFun w i := e.symm (fun j => w (i, j))
  left_inv v := by funext i; exact e.symm_apply_apply (v i)
  right_inv w := by
    funext p
    change e (e.symm (fun j => w (p.1, j))) p.2 = w p
    rw [e.apply_symm_apply]
  map_add' v w := by funext p; simp
  map_smul' c v := by funext p; simp

/-- Binary coordinates on the literal right-coset model. -/
def nativeBinaryCoordinates (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2)) :
    CoordinateSpace false ≃ₗ[ZMod 2] BinarySpace :=
  coordinateSectionEquiv.toLinearEquiv.trans (pointCoordinates e)

/-- One nonzero fiber block in each block row, with the inverse source point. -/
def sparseMatrix (j : Fin 2)
    (blocks : Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2)) :
    Matrix BinaryIndex BinaryIndex (ZMod 2) :=
  fun p q => if q.1 = generatorPoint j p.1 then blocks p.1 p.2 q.2 else 0

theorem sparseMatrix_mulVec (j : Fin 2)
    (blocks : Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2))
    (v : BinarySpace) (p : Fin 22) (a : Fin 9) :
    (sparseMatrix j blocks).mulVec v (p, a) =
      (blocks p).mulVec (fun b => v (generatorPoint j p, b)) a := by
  simp [Matrix.mulVec, dotProduct, sparseMatrix, Fintype.sum_prod_type, ite_mul]

/-- The generator convention of the shared transversal is the literal actor. -/
theorem generator_eq_actor (j : Fin 2) : generator j = actor j := by
  fin_cases j <;> rfl

/-- The local correction equations yield the exact native generator matrices. -/
theorem nativeBinaryCoordinates_generator
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2))
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hb : ∀ j p v, e (Models.pointAction false (generatorCorrection j p) v) =
      (blocks j p).mulVec (e v)) (j : Fin 2) (v : CoordinateSpace false) :
    nativeBinaryCoordinates e (coordinateAction false (actor j) v) =
      (sparseMatrix j (blocks j)).mulVec (nativeBinaryCoordinates e v) := by
  have h := LinearMap.congr_fun (coordinateSectionEquiv.isIntertwining' (generator j)) v
  change coordinateSectionEquiv (coordinateAction false (generator j) v) =
    sectionAction (generator j) (coordinateSectionEquiv v) at h
  rw [← generator_eq_actor]
  change pointCoordinates e (coordinateSectionEquiv (coordinateAction false (generator j) v)) = _
  rw [h]
  funext p
  rcases p with ⟨p, a⟩
  change e (sectionAction (generator j) (coordinateSectionEquiv v) p) a = _
  rw [sectionAction_generator, hb, sparseMatrix_mulVec]
  rfl

/-- Inverse certificates between the native block indexing and the saved indexing. -/
def savedCoordinates
    (C : Matrix (Fin 198) BinaryIndex (ZMod 2))
    (D : Matrix BinaryIndex (Fin 198) (ZMod 2))
    (hDC : D * C = 1) (hCD : C * D = 1) : BinarySpace ≃ₗ[ZMod 2] Space :=
  { C.mulVecLin with
    invFun := D.mulVec
    left_inv v := by
      change D.mulVec (C.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec]
    right_inv v := by
      change C.mulVec (D.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hCD, Matrix.one_mulVec] }

theorem savedCoordinates_apply
    (C : Matrix (Fin 198) BinaryIndex (ZMod 2))
    (D : Matrix BinaryIndex (Fin 198) (ZMod 2))
    (hDC : D * C = 1) (hCD : C * D = 1) (v : BinarySpace) :
    savedCoordinates C D hDC hCD v = C.mulVec v := by
  change C.mulVecLin v = C.mulVec v
  exact Matrix.mulVecLin_apply C v

/-- Finite inverse and intertwining matrix identities construct the requested
native comparison. The matrices are certificates still to be supplied. -/
theorem generator_coordinates_of_block_certificates
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2))
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hb : ∀ j p v, e (Models.pointAction false (generatorCorrection j p) v) =
      (blocks j p).mulVec (e v))
    (i : Fin 2) (C : Matrix (Fin 198) BinaryIndex (ZMod 2))
    (D : Matrix BinaryIndex (Fin 198) (ZMod 2))
    (hDC : D * C = 1) (hCD : C * D = 1)
    (hC : ∀ j, C * sparseMatrix j (blocks j) = generatorMatrix i j * C) :
    ∃ e' : CoordinateSpace false ≃ₗ[ZMod 2] Space,
      ∀ j v, e' (coordinateAction false (actor j) v) =
        (generatorMatrix i j).mulVec (e' v) := by
  refine ⟨(nativeBinaryCoordinates e).trans (savedCoordinates C D hDC hCD), ?_⟩
  intro j v
  simp only [LinearEquiv.trans_apply, savedCoordinates_apply]
  rw [nativeBinaryCoordinates_generator e blocks hb,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hC]

/-- Actual application to the literal invariant flag, with no factor-density
assumption and no assertion that the certificate premises have been discharged. -/
theorem flag_of_block_certificates
    (e : Models.HermitianSpace ≃ₗ[ZMod 2] (Fin 9 → ZMod 2))
    (blocks : Fin 2 → Fin 22 → Matrix (Fin 9) (Fin 9) (ZMod 2))
    (hb : ∀ j p v, e (Models.pointAction false (generatorCorrection j p) v) =
      (blocks j p).mulVec (e v))
    (i : Fin 2) (C : Matrix (Fin 198) BinaryIndex (ZMod 2))
    (D : Matrix BinaryIndex (Fin 198) (ZMod 2))
    (hDC : D * C = 1) (hCD : C * D = 1)
    (hC : ∀ j, C * sparseMatrix j (blocks j) = generatorMatrix i j * C) :
    Nonempty (FlagCoordinates i) := by
  obtain ⟨e', he'⟩ :=
    generator_coordinates_of_block_certificates e blocks hb i C D hDC hCD hC
  exact ⟨flagOfGeneratorCoordinates i e' he'⟩

end NativeComparison
end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration

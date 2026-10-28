module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement.Lifts

/-!
# Root placement of normalized elementary adjoint actors

For every normalized graph action, the inner actors have commuting involutory
matrix lifts preserving the literal Gram matrix. An explicit isometry places
these lifts in one upper root group. Conjugating the original normalized linear
equivalence by that same matrix gives exactly `coordinateEquiv`, and the matrix
identities for the root and graph operators give the published pointwise
parameters. No lifting, fixed-space, conjugacy, or normal-form premise remains.

This proves `RootPlacement`, including binary fields of degrees one and two.
The original outer-actor assembly consumes it through
`graph_forms_of_rootPlacement`; operator coverage remains with its independent
source owner.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
open Matrix
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

private lemma matrixOf_injective : Function.Injective (matrixOf B.Carrier) := by
  intro x y h
  apply (coordinates B.Carrier).symm.injective
  apply matrix_injective
  simpa only [← matrixOf_coordinates, LinearEquiv.apply_symm_apply] using h

/-- Simultaneous root placement for the actual normalized adjoint actors,
including binary fields of degrees one and two. -/
theorem root_placement : RootPlacement B σ := by
  classical
  intro A hA N
  obtain ⟨s, bit, hs, hJ, hc, ht⟩ := RootPlacement.exists_lifted_actors B σ A hA N
  obtain ⟨C, hC, hroot⟩ := RootPlacement.isometry_root_placement s hs hJ hc
  refine ⟨C, hC, fun t => ?_⟩
  obtain ⟨a, ha⟩ := hroot t
  have hsi : (s t)⁻¹ = s t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs t)
  have hki : ((C * s t * C⁻¹)⁻¹).val = unipotent B.Carrier a := by
    simpa only [_root_.mul_inv_rev, inv_inv, hsi, mul_assoc] using ha
  have hp (X : Mat (F := B.Carrier)) : inner C (inner (s t) X) =
      unipotent B.Carrier a * inner C X * unipotent B.Carrier a := by
    rw [inner_conj]
    change (C * s t * C⁻¹).val * inner C X * ((C * s t * C⁻¹)⁻¹).val = _
    rw [ha, hki]
  have hm (x : AdjointSpace B.Carrier) :
      matrixOf B.Carrier (coordinates B.Carrier (adjointConj C x)) = inner C (matrix x) := by
    rw [matrixOf_coordinates]
    exact matrix_adjointConj C x
  refine ⟨(a, bit t), fun v => ?_⟩
  apply matrixOf_injective B
  change matrixOf B.Carrier (coordinates B.Carrier (adjointConj C (N.equiv (t.val.val.val v)))) =
    matrixOf B.Carrier (operator B.Carrier (a, bit t)
      (coordinates B.Carrier (adjointConj C (N.equiv v))))
  rw [hm, ht]
  simp only [operator]
  split_ifs with hb
  · rw [matrixOf_shearCoordinates, hm, hp]
  · rw [matrixOf_shearCoordinates, matrixOf_graphCoordinates,
      hm, hp]
    let J : GL (Fin 3) B.Carrier :=
      ⟨gram B.Carrier, gram B.Carrier, gram_sq B.Carrier, gram_sq B.Carrier⟩
    have he := graph_conj_gram C J hC (matrix (N.equiv v))
    change inner C (gram B.Carrier * (matrix (N.equiv v)).transpose * gram B.Carrier) = _ at he
    rw [he]

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer

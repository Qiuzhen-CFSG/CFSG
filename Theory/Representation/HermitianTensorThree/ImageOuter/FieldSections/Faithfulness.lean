module

public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Centralizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Coordinates

/-!
# Faithfulness on the three actual field sections

On the moved space the elementary alternating matrices detect every entry
of the adjugate of the fixed-field matrix. On the middle quotient the
symmetric diagonal matrices detect every squared matrix entry. These tests
prove faithfulness directly for the inherited actions. The commutator map
identifies the top quotient equivariantly with the moved space.

Source: Aschbacher–Smith H.4.4(6), printed p.381.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.FieldSections
variable (n : ℕ) [NeZero n]

private theorem adjugate_eq_one_of_fixes_symmetricUnits (A : Mat n)
    (hA : ∀ i j, sigma n (A i j) = A i j)
    (h : ∀ i j, A * (symmetricUnit n i j).val * adjoint n A =
      (symmetricUnit n i j).val) : A.adjugate = 1 := by
  let p : Fin 3 → Fin 3 := ![1,0,0]
  let q : Fin 3 → Fin 3 := ![2,2,1]
  have hminor (i j a b : Fin 3) :
      A a i * A b j + A a j * A b i = (symmetricUnit n i j).val a b := by
    have he := congrArg (fun B : Mat n => B a b) (h i j)
    simpa only [symmetricUnit_congruence, hA] using he
  ext i j
  have he := hminor (p i) (q i) (p j) (q j)
  fin_cases i <;> fin_cases j <;>
    simpa [p, q, Matrix.adjugate_fin_three, symmetricUnit, Matrix.single_apply,
      CharTwo.sub_eq_add, CharTwo.neg_eq, mul_comm] using he

/-- No nonidentity element acts trivially on the literal commutator space. -/
theorem movedAction_faithful : Function.Injective (movedAction n) := by
  apply (injective_iff_map_eq_one (movedAction n)).mpr
  intro g hg
  obtain ⟨a, rfl⟩ := fixedToCentralizer_surjective n g
  suffices ha : fixedCover n a = 1 by
    apply Subtype.ext
    change binaryActionHom n (fixedCover n a) = 1
    rw [ha, map_one]
  have hfix (i j : Fin 3) :
      (fixedCover n a).val * (symmetricUnit n i j).val * adjoint n (fixedCover n a).val =
        (symmetricUnit n i j).val := by
    have he := congrArg
      (fun f : (moved n) →ₗ[F n] moved n =>
        (f ⟨symmetricUnit n i j, symmetricUnit_mem_moved n i j⟩).val.val) hg
    rw [movedAction_apply, fixedToCentralizer_apply] at he
    exact he
  have had := adjugate_eq_one_of_fixes_symmetricUnits n (fixedCover n a).val
    (fun i j => (a.val i j).property) hfix
  apply inv_eq_one.mp
  apply Subtype.ext
  exact had

/-- No nonidentity element acts trivially on C_V(σ)/[V,σ]. -/
theorem middleAction_faithful : Function.Injective (middleAction n) := by
  apply (injective_iff_map_eq_one (middleAction n)).mpr
  intro g hg
  obtain ⟨a, rfl⟩ := fixedToCentralizer_surjective n g
  have hentry (i j : Fin 3) : (fixedCover n a).val i j = (1 : Mat n) i j := by
    let X : fieldFixed n := ⟨diagonalUnit n j, diagonalUnit_mem_fixed n j⟩
    have he := congrArg (fun f : ((fieldFixed n) ⧸ movedInFixed n) →ₗ[F n]
      ((fieldFixed n) ⧸ movedInFixed n) => f ((movedInFixed n).mkQ X)) hg
    change (movedInFixed n).mkQ (fixedAction n (fixedToCentralizer n a) X) =
      (movedInFixed n).mkQ X at he
    have hm : fixedAction n (fixedToCentralizer n a) X - X ∈ movedInFixed n :=
      (Submodule.Quotient.eq _).mp he
    have hd := moved_diagonal_zero n
      ⟨(fixedAction n (fixedToCentralizer n a) X).val - X.val, hm⟩ i
    change (fixedAction n (fixedToCentralizer n a) X).val.val i i - X.val.val i i = 0 at hd
    rw [fixedAction_apply, fixedToCentralizer_apply] at hd
    change ((fixedCover n a).val * (diagonalUnit n j).val *
      adjoint n (fixedCover n a).val) i i - (diagonalUnit n j).val i i = 0 at hd
    rw [diagonalUnit_congruence] at hd
    have hs : (fixedCover n a).val i j * sigma n ((fixedCover n a).val i j) =
        (diagonalUnit n j).val i i := by
      apply sub_eq_zero.mp
      exact hd
    rw [show sigma n ((fixedCover n a).val i j) = (fixedCover n a).val i j from
      (a.val i j).property] at hs
    apply frobenius_inj (E n) 2
    change ((fixedCover n a).val i j) ^ 2 = ((1 : Mat n) i j) ^ 2
    simpa [pow_two, diagonalUnit, Matrix.single_apply, Matrix.one_apply, eq_comm] using hs
  apply Subtype.ext
  change binaryActionHom n (fixedCover n a) = 1
  have ha : fixedCover n a = 1 := Subtype.ext (Matrix.ext hentry)
  rw [ha, map_one]

/-- The actual commutator map identifies V/C_V(σ) with [V,σ]. -/
def topToMoved : ((Space n) ⧸ fieldFixed n) ≃ₗ[F n] moved n :=
  ((fieldSwap n).toLinearMap - LinearMap.id).quotKerEquivRange

theorem topToMoved_mk (X : Space n) :
    (topToMoved n ((fieldFixed n).mkQ X)).val = fieldSwap n X - X := rfl

theorem topToMoved_intertwines (g : centralizer n) (X : (Space n) ⧸ fieldFixed n) :
    topToMoved n (topAction n g X) = movedAction n g (topToMoved n X) := by
  induction X using Submodule.Quotient.induction_on with
  | _ X =>
    apply Subtype.ext
    change fieldSwap n (centralizerAction n g X) - centralizerAction n g X =
      centralizerAction n g (fieldSwap n X - X)
    rw [map_sub, centralizerAction_commutes]

/-- Faithfulness of the actual action on V/C_V(σ). -/
theorem topAction_faithful : Function.Injective (topAction n) := by
  apply (injective_iff_map_eq_one (topAction n)).mpr
  intro g hg
  apply (injective_iff_map_eq_one (movedAction n)).mp (movedAction_faithful n) g
  apply LinearMap.ext
  intro X
  obtain ⟨Y, rfl⟩ := (topToMoved n).surjective X
  rw [← topToMoved_intertwines, hg]
  rfl

end Representation.HermitianTensorThree.ImageOuter.FieldSections

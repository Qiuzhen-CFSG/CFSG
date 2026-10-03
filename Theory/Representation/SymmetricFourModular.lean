module

public import Theory.SpecificGroups.SymmetricFourConjugacy
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# The two-dimensional characteristic-two representation of S₄

Identify the four letters with the affine plane over `ZMod 2`. Every permutation
is affine, and taking its linear part gives a homomorphism to `GL(2, 2)`.
We verify the finite matrix identity by kernel reduction, then extend its
coefficients to any field of characteristic two. Two transpositions give the
opposite elementary shears. Their differences from the identity extract both
coordinate lines from any nonzero invariant subspace, proving irreducibility.
The three-cycle has characteristic polynomial `X² + X + 1`.

This is the degree-two simple module in Fong, *Some Sylow subgroups of order 32*,
J. Algebra 6 (1967), p. 71. The affine construction is an equivalent model of the
action on the three pair partitions.
-/

public section

open Matrix
namespace SymmetricFourModular

abbrev Group := Equiv.Perm (Fin 4)

private def point (k : Fin 4) : Fin 2 → ZMod 2 := ![(k.val % 2 : ℕ), (k.val / 2 : ℕ)]
private def matrix (g : Group) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => point (g (if j = 0 then 1 else 2)) i - point (g 0) i
private theorem matrix_one : matrix 1 = 1 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem matrix_mul : ∀ g h : Group, matrix (g * h) = matrix g * matrix h := by decide

variable (F : Type*) [Field F] [CharP F 2]
/-- The linear-part representation, with coefficients extended from F₂. -/
noncomputable def rep : Representation F Group (Fin 2 → F) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) F ≃ₐ[F] _).toMonoidHom.comp
    ((ZMod.castHom (dvd_refl 2) F).mapMatrix.toMonoidHom.comp
      { toFun := matrix
        map_one' := matrix_one
        map_mul' := matrix_mul })

/-- The transposition of the origin and the first basis point is an upper shear. -/
theorem upper_apply (v : Fin 2 → F) : rep F (Equiv.swap 0 1) v = ![v 0 + v 1, v 1] := by
  have hm : matrix (Equiv.swap 0 1) = !![1, 1; 0, 1] := by decide
  ext i
  fin_cases i <;>
    simp [rep, hm, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The transposition of the origin and the second basis point is a lower shear. -/
theorem lower_apply (v : Fin 2 → F) : rep F (Equiv.swap 0 2) v = ![v 0, v 0 + v 1] := by
  have hm : matrix (Equiv.swap 0 2) = !![1, 0; 1, 1] := by decide
  ext i
  fin_cases i <;>
    simp [rep, hm, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Opposite shears generate both coordinate lines from any nonzero vector. -/
theorem irreducible : Representation.IsIrreducible (rep F) := by
  classical
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hne : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := S.toSubmodule.ne_bot_iff.mp hne
  have hu (w : Fin 2 → F) (hw : w ∈ S.toSubmodule) : ![w 1, 0] ∈ S.toSubmodule := by
    have h := S.toSubmodule.sub_mem (S.apply_mem_toSubmodule (Equiv.swap 0 1) hw) hw
    rw [upper_apply] at h
    convert h using 1
    ext i
    fin_cases i <;> simp
  have hl (w : Fin 2 → F) (hw : w ∈ S.toSubmodule) : ![0, w 0] ∈ S.toSubmodule := by
    have h := S.toSubmodule.sub_mem (S.apply_mem_toSubmodule (Equiv.swap 0 2) hw) hw
    rw [lower_apply] at h
    convert h using 1
    ext i
    fin_cases i <;> simp
  have he0 : ![1, 0] ∈ S.toSubmodule := by
    by_cases hv1 : v 1 = 0
    · have hvne : v 0 ≠ 0 := by
        intro hvz
        apply hv0
        ext i
        fin_cases i <;> simp [hvz, hv1]
      have h := S.toSubmodule.smul_mem (v 0)⁻¹ (hu _ (hl v hv))
      simpa [hvne] using h
    · have h := S.toSubmodule.smul_mem (v 1)⁻¹ (hu v hv)
      simpa [hv1] using h
  have he1 : ![0, 1] ∈ S.toSubmodule := hl _ he0
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  have h := S.toSubmodule.add_mem (S.toSubmodule.smul_mem (w 0) he0)
    (S.toSubmodule.smul_mem (w 1) he1)
  convert h using 1
  ext i
  fin_cases i <;> simp

open Polynomial in
/-- The nonidentity odd-order class has the third cyclotomic polynomial. -/
theorem charpoly_threeCycle : (rep F SymmetricFourConjugacy.threeCycle).charpoly = X ^ 2 + X + 1 := by
  have hm : matrix SymmetricFourConjugacy.threeCycle = !![1, 1; 1, 0] := by decide
  change ((matrix SymmetricFourConjugacy.threeCycle).map
    (ZMod.castHom (dvd_refl 2) F)).toLin'.charpoly = _
  rw [hm, Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two, CharTwo.sub_eq_add]
end SymmetricFourModular

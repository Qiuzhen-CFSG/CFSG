module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

/-!
# Coordinates on the actual binary M₁₂ heart

Coordinate i of the augmentation quotient is v_i + v_10. Every coordinate
vector x has the even representative (x_0,...,x_9,0,Σx_i). This constructs
the basis represented by e_i + e_11 and identifies the literal permutation
action with its ten by ten matrices.

This is the coordinate calculation used in the fixed-point extension argument
for James's binary M₁₂ module, cited in Aschbacher--Smith G.7.3(2), p.348.
-/

@[expose] public section
open BinaryPermutation
namespace Representation.MathieuSmall.M12Recognition.PointExtension
abbrev V10 := Fin 10 → ZMod 2

def rawCoordinates : Full (Fin 12) →ₗ[ZMod 2] V10 where
  toFun v i := v (Fin.castAdd 2 i) + v 10
  map_add' _ _ := by ext i; simp; ring
  map_smul' _ _ := by ext i; simp [mul_add]

noncomputable def deletedCoordinates : Deleted (Fin 12) →ₗ[ZMod 2] V10 :=
  (constants (Fin 12)).liftQ rawCoordinates (by
    rw [constants, Submodule.span_le, Set.singleton_subset_iff]
    change rawCoordinates (allOne (Fin 12)) = 0
    ext i
    change (1 : ZMod 2) + 1 = 0
    decide)

noncomputable def coordinates : M12Heart →ₗ[ZMod 2] V10 :=
  deletedCoordinates.comp (natural (Fin 12)).subtype

def representative (v : V10) : Full (Fin 12) :=
  fun x => if hx : x.val < 10 then v ⟨x.val, hx⟩ else if x = 11 then ∑ i, v i else 0

theorem representative_mem (v : V10) : representative v ∈ core (Fin 12) := by
  rw [mem_core]
  simp [representative, Fin.sum_univ_succ]
  ring_nf
  simp [CharTwo.two_eq_zero]

noncomputable def sectionVector (v : V10) : M12Heart :=
  ⟨(constants (Fin 12)).mkQ (representative v),
    ⟨representative v, representative_mem v, rfl⟩⟩

theorem coordinates_section (v : V10) : coordinates (sectionVector v) = v := by
  ext i
  change rawCoordinates (representative v) i = v i
  fin_cases i <;> simp [rawCoordinates, representative]

noncomputable def coordinateEquivalence : M12Heart ≃ₗ[ZMod 2] V10 :=
  LinearEquiv.ofBijective coordinates (by
    have hs : Function.Surjective coordinates := fun v => ⟨sectionVector v, coordinates_section v⟩
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [finrank_m12Heart] : Module.finrank (ZMod 2) M12Heart =
          Module.finrank (ZMod 2) V10)).mpr hs, hs⟩)

noncomputable def matrixEquivalence : Module.End (ZMod 2) M12Heart ≃ₐ[ZMod 2]
    Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  (coordinateEquivalence.conjAlgEquiv (ZMod 2)).trans LinearMap.toMatrixAlgEquiv'

theorem coordinateEquivalence_symm (v : V10) :
    coordinateEquivalence.symm v = sectionVector v := by
  apply coordinateEquivalence.injective
  exact (coordinateEquivalence.apply_symm_apply v).trans (coordinates_section v).symm

theorem matrix_natural (g : Equiv.Perm (Fin 12)) (i j : Fin 10) :
    matrixEquivalence (naturalRepresentation (Fin 12) g) i j =
      rawCoordinates (representation (Fin 12) g (representative (Pi.single j 1))) i := by
  change coordinates (naturalRepresentation (Fin 12) g
    (coordinateEquivalence.symm (Pi.single j 1))) i = _
  rw [coordinateEquivalence_symm]
  rfl

/-- Matrix in the basis represented by e_i + e_11, for i < 10. -/
def permutationMatrix (g : Equiv.Perm (Fin 12)) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => rawCoordinates (representation (Fin 12) g (representative (Pi.single j 1))) i

theorem matrix_natural_eq (g : Equiv.Perm (Fin 12)) :
    matrixEquivalence (naturalRepresentation (Fin 12) g) = permutationMatrix g := by
  ext i j
  exact matrix_natural g i j


private theorem representative_single (j : Fin 10) (x : Fin 12) :
    representative (Pi.single j (1 : ZMod 2)) x =
      (if x = Fin.castAdd 2 j then 1 else 0) + (if x = 11 then 1 else 0) := by
  by_cases hx : x.val < 10
  · have hn : x ≠ 11 := by intro e; subst x; norm_num at hx
    simp [representative, hx, hn, Pi.single_apply, Fin.ext_iff]
  · have hn : x ≠ Fin.castAdd 2 j := by
      intro e
      subst x
      exact hx j.isLt
    simp [representative, hx, hn]

private theorem inverse_entry (g : Equiv.Perm (Fin 12)) (x y : Fin 12) :
    (g.symm x = y) ↔ (x = g y) := by
  rw [_root_.Equiv.symm_apply_eq]

theorem permutationMatrix_formula (g : Equiv.Perm (Fin 12)) (i j : Fin 10) :
    permutationMatrix g i j =
      ((if Fin.castAdd 2 i = g (Fin.castAdd 2 j) then 1 else 0) +
        (if Fin.castAdd 2 i = g 11 then 1 else 0)) +
      ((if (10 : Fin 12) = g (Fin.castAdd 2 j) then 1 else 0) +
        (if (10 : Fin 12) = g 11 then 1 else 0)) := by
  change representative (Pi.single j 1) (g.symm (Fin.castAdd 2 i)) +
    representative (Pi.single j 1) (g.symm 10) = _
  simp only [representative_single, inverse_entry]
end Representation.MathieuSmall.M12Recognition.PointExtension

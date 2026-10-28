module
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement
public import Theory.Representation.CommutingCentralizersCohomology

/-!
# First cohomology of the binary determinant module

The cubic matrix with rows `(0,1)` and `(1,1)` has no fixed vectors. Its
left and right actions commute and each is fixed-point-free on the matrix
space. Their centralizers contain the opposite factors, hence generate the
whole product. Subtracting a principal cocycle and applying this twice
shows that every cocycle is principal.

Source: Aschbacher--Smith 9.2.2, printed p.730. This is the quotient-action
cohomology input; it does not assert vanishing before quotienting the
original actor by its two-core.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Representation.OneCohomology

private def cubic : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private lemma cubic_fixed_left (M : V) (h : action (cubic, 1) M = M) : M = 0 := by
  rw [Displacement.fixed_iff_intertwines] at h
  simp only [SpecialLinearGroup.coe_one, mul_one] at h
  apply Matrix.ext
  intro i j
  have h0 : M 1 j = M 0 j := by
    simpa [cubic, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun N : V => N 0 j) h
  have h1 : M 0 j = 0 := by
    simpa [cubic, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun N : V => N 1 j) h
  fin_cases i
  · exact h1
  · exact h0.trans h1

private lemma cubic_fixed_right (M : V) (h : action (1, cubic) M = M) : M = 0 := by
  rw [Displacement.fixed_iff_intertwines] at h
  simp only [SpecialLinearGroup.coe_one, one_mul] at h
  apply Matrix.ext
  intro i j
  have h0 : M i 0 = M i 1 := by
    simpa [cubic, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun N : V => N i 0) h
  have h1 : M i 0 = 0 := by
    simpa [cubic, Matrix.mul_apply, Fin.sum_univ_two] using
      (congrArg (fun N : V => N i 1) h).symm
  fin_cases j
  · exact h1
  · exact h0.symm.trans h1

/-- A first-factor element fixes no nonzero tensor. This places the original
tensor module inside its first component via the commutator criterion. -/
theorem exists_left_fixedPointFree :
    ∃ a : SpecialLinearGroup (Fin 2) F, ∀ M : V, action (a, 1) M = M → M = 0 :=
  ⟨cubic, cubic_fixed_left⟩

/-- Every crossed homomorphism for the actual binary determinant action is principal. -/
theorem tensor_subsingleton_H1 : Subsingleton (H1 action) := by
  apply subsingleton_H1_of_commuting_centralizers action (cubic, 1) (1, cubic)
  · change (cubic, 1) * (1, cubic) = (1, cubic) * (cubic, 1)
    simp
  · exact cubic_fixed_left
  · exact cubic_fixed_right
  · apply top_unique
    rintro ⟨g,h⟩ _
    have hx : (g, (1 : SpecialLinearGroup (Fin 2) F)) ∈
        Subgroup.centralizer ({(1, cubic)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    have hy : ((1 : SpecialLinearGroup (Fin 2) F), h) ∈
        Subgroup.centralizer ({(cubic, 1)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    simpa using Subgroup.mul_mem
      (Subgroup.centralizer ({(cubic,1)} : Set G) ⊔
        Subgroup.centralizer ({(1,cubic)} : Set G))
      (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hy)

end ClassicalOrthogonal.FourPlusMatrix.Binary

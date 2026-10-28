module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.PlaneBasis.Frame

/-!
# Completing two Hermitian pairs in dimension five

The span of four paired vectors has a nonzero perpendicular. A nonzero vector
there completes an invertible matrix, as its kernel is killed successively by
the four pairings. Ambient nondegeneracy forces its norm to be nonzero, and
finite-field norm surjectivity scales it to norm one. The resulting Gram matrix
is precisely the published plane reference matrix.

This is the complement step in the unitary-five instance of GLS3 Lemma 2.7.1,
printed p.89, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section

open Matrix Module BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.PlaneBasis
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

def completeMatrix (v : Fin 4 → Fin 5 → F) (z : Fin 5 → F) : Matrix (Fin 5) (Fin 5) F :=
  fun i j => (![v 0, v 1, v 2, v 3, z] j) i

lemma completeMatrix_mulVec (v : Fin 4 → Fin 5 → F) (z x : Fin 5 → F) :
    completeMatrix v z *ᵥ x =
      x 0 • v 0 + x 1 • v 1 + x 2 • v 2 + x 3 • v 3 + x 4 • z := by
  ext i
  simp [completeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    smul_eq_mul, mul_comm, add_assoc]
  ring

lemma completeMatrix_isUnit (v : Fin 4 → Fin 5 → F)
    (hv : ∀ i j, pairing J (v i) (v j) = gramFour i j)
    (z : Fin 5 → F) (hz : ∀ i, pairing J (v i) z = 0) (hz0 : z ≠ 0) :
    IsUnit (completeMatrix v z) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (completeMatrix v z).mulVecLin
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change completeMatrix v z *ᵥ x = 0 at hx
  have he (i : Fin 4) := congrArg (pairing J (v i)) hx
  simp only [completeMatrix_mulVec, pair_add_right, pair_smul_right, hv, hz,
    pair_zero_right, mul_zero, add_zero] at he
  have h1 : x 1 = 0 := by simpa [gramFour] using he 0
  have h3 : x 3 = 0 := by simpa [gramFour] using he 2
  have h0 : x 0 = 0 := by simpa [gramFour, h1] using he 1
  have h2 : x 2 = 0 := by simpa [gramFour, h3] using he 3
  have h4 : x 4 = 0 := by
    rw [completeMatrix_mulVec, h0, h1, h2, h3] at hx
    simp only [zero_smul, zero_add] at hx
    exact (smul_eq_zero.mp hx).resolve_right hz0
  ext i
  fin_cases i <;> assumption

lemma exists_complement_unit [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (v : Fin 4 → Fin 5 → F)
    (hv : ∀ i j, pairing J (v i) (v j) = gramFour i j) :
    ∃ z : Fin 5 → F, pairing J z z = 1 ∧ ∀ i, pairing J (v i) z = 0 := by
  classical
  let H := Submodule.span F (Set.range v)
  have hd : finrank F H ≤ 4 := finrank_range_le_card v
  have hn : orthogonal J H ≠ ⊥ := by
    intro hh
    have hk := finrank_orthogonal J H
    rw [hh, finrank_bot] at hk
    omega
  obtain ⟨z, hz, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hzi (i : Fin 4) : pairing J (v i) z = 0 :=
    hz _ (Submodule.subset_span ⟨i, rfl⟩)
  have hnz : pairing J z z ≠ 0 := by
    intro hh
    apply hzne
    apply pair_nondegenerate J
    intro w
    obtain ⟨x, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      (completeMatrix_isUnit J v hv z hzi hzne) w
    simp only [completeMatrix_mulVec, pair_add_left, pair_smul_left, hzi, hh,
      mul_zero, add_zero]
  obtain ⟨a, _, ha⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective J 4
    hcard (fixed_card_four J hcard hconj) (pairing J z z)⁻¹
    (by rw [map_inv₀, pair_self_fixed]) (inv_ne_zero hnz)
  refine ⟨a • z, ?_, ?_⟩
  · rw [pair_smul_left, pair_smul_right]
    calc
      J.conj a * (a * pairing J z z) = (a * J.conj a) * pairing J z z := by ring
      _ = 1 := by rw [ha, inv_mul_cancel₀ hnz]
  · intro i
    rw [pair_smul_right, hzi, mul_zero]

lemma completeMatrix_gram (v : Fin 4 → Fin 5 → F)
    (hv : ∀ i j, pairing J (v i) (v j) = gramFour i j)
    (z : Fin 5 → F) (hzz : pairing J z z = 1)
    (hz : ∀ i, pairing J (v i) z = 0) :
    J.conjTranspose (completeMatrix v z) * completeMatrix v z = referenceGram true := by
  have hzr (i : Fin 4) : pairing J z (v i) = 0 := by
    simpa using pair_reverse J (hz i)
  have he (i j : Fin 5) :
      (J.conjTranspose (completeMatrix v z) * completeMatrix v z) i j =
        pairing J (![v 0, v 1, v 2, v 3, z] i) (![v 0, v 1, v 2, v 3, z] j) := rfl
  ext i j
  rw [he]
  fin_cases i <;> fin_cases j <;> simp [hv, hz, hzr, hzz, gramFour, referenceGram]

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.PlaneBasis

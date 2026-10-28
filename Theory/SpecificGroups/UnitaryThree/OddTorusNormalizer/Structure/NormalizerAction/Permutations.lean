module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.NormalizerGeometry

/-!
# Permutation representatives in the special unitary frame stabilizer

In characteristic two every permutation matrix is unitary of determinant one
for the identity Gram form. Conjugation by the supplied orthonormal frame
therefore gives representatives of all six coordinate permutations in the
actual special group. The geometric action on these representatives is the
original permutation, proving surjectivity. The characteristic-two instance
is also recovered from the prescribed binary field cardinality.

Source: GLS4, Chapter 4, Lemma 3.11(c), used in Chapter 2, Lemma 17.4.
-/

@[expose] public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open scoped Pointwise
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

def permutationGL : Equiv.Perm (Fin 3) →* GL (Fin 3) E :=
  (Matrix.permMatrixHom (n := Fin 3) (R := E)).toHomUnits

theorem permutationGL_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (permutationGL (E := E) σ).val i j = if i = σ j then 1 else 0 := by
  change ((σ⁻¹).permMatrix E) i j = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem permutationGL_mem (σ : Equiv.Perm (Fin 3)) :
    permutationGL (E := E) σ ∈ coordinateStabilizer := by
  have hs (τ : Equiv.Perm (Fin 3)) : ∀ i, ∃ j,
      (permutationGL (E := E) τ).val j i ≠ 0 ∧
      ∀ k, k ≠ j → (permutationGL (E := E) τ).val k i = 0 := by
    intro i
    exact ⟨τ i, by simp [permutationGL_apply], fun k hk => by simp [permutationGL_apply, hk]⟩
  exact mem_coordinateStabilizer_of_column_support _ (hs σ) (by
    simpa only [map_inv] using hs σ⁻¹)

theorem permutationGL_special [CharP E 2] (J : HermitianForm 3 E)
    (σ : Equiv.Perm (Fin 3)) : permutationGL σ ∈ (identityGram J).specialSubgroup := by
  rw [mem_specialSubgroup_iff]
  have hadj : (identityGram J).conjTranspose (permutationGL (E := E) σ).val =
      (permutationGL (E := E) σ⁻¹).val := by
    ext i j
    change J.conj ((permutationGL (E := E) σ).val j i) = _
    simp only [permutationGL_apply, Equiv.Perm.inv_def]
    by_cases h : j = σ i
    · subst j; simp
    · have hi : i ≠ σ.symm j := by
        intro hi
        apply h
        rw [hi, σ.apply_symm_apply]
      simp [h, hi]
  constructor
  · rw [identityGram_form, mul_one, hadj, map_inv]
    exact Units.inv_mul _
  · apply Units.ext
    change ((σ⁻¹).permMatrix E).det = 1
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;>
      simp [h, CharTwo.neg_eq]

def specialPermutation [CharP E 2] (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Equiv.Perm (Fin 3) →* J.specialSubgroup :=
  ((MulAut.conj P.val).toMonoidHom.comp permutationGL).codRestrict J.specialSubgroup
    (fun σ => (special_conjugate_iff J P.val _ P.property).mpr (permutationGL_special J σ))

theorem specialPermutation_coordinates [CharP E 2]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (σ : Equiv.Perm (Fin 3)) :
    frameCoordinateHom J P (specialPermutation J P σ) = permutationGL σ := by
  change P.val⁻¹ * (P.val * permutationGL σ * P.val⁻¹) * (P.val⁻¹)⁻¹ = _
  simp [mul_assoc]

def monomialPermutation [CharP E 2] (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Equiv.Perm (Fin 3) →* specialFrameMonomial J P :=
  (specialPermutation J P).codRestrict (specialFrameMonomial J P) (fun σ => by
    change frameCoordinateHom J P (specialPermutation J P σ) ∈ coordinateStabilizer
    rw [specialPermutation_coordinates]
    exact permutationGL_mem σ)

theorem specialMonomialAction_permutation [CharP E 2]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (σ : Equiv.Perm (Fin 3)) :
    specialMonomialAction J P (monomialPermutation J P σ) = σ := by
  apply Equiv.ext
  intro i
  apply coordinateIndex_eq_of_ne_zero
  change (frameCoordinateHom J P (specialPermutation J P σ)).val (σ i) i ≠ 0
  rw [specialPermutation_coordinates, permutationGL_apply]
  simp

theorem specialMonomialAction_surjective [CharP E 2]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Function.Surjective (specialMonomialAction J P) :=
  fun σ => ⟨monomialPermutation J P σ, specialMonomialAction_permutation J P σ⟩

theorem frame_char_two [Finite E] (n : ℕ) (hcard : Nat.card E = (2 ^ n) ^ 2) : CharP E 2 := by
  let := Fintype.ofFinite E
  exact charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)

end UnitaryThree.OddTorusNormalizer

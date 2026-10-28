module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction
public import Theory.Character.ScalarProductMultiplicity

/-!
# Degrees and orthogonality of signed irreducibles

A sign changes the degree to an integer, without changing the positive natural
number attached to the underlying irreducible character. Signed terms remain
orthonormal and orthogonal to the principal character. Suzuki's individual
summand can be written as the square of the signed value divided by the signed
degree; the denominator's sign must be retained.

Source: ordinary character orthogonality and Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Lemmas 11–12, pp.12–14.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
variable {G : Type*} [Group G] [Finite G]

namespace SignedFamily
variable {n : ℕ} (F : SignedFamily G n)

/-- The signed degree, distinguished from the positive irreducible degree. -/
@[expose] public def signedDegree (j : Fin n) : ℤ :=
  F.sign j * ((F.irreducible j).degree : ℤ)

omit [Finite G] in
public theorem term_one (j : Fin n) : F.term j 1 = (F.signedDegree j : ℂ) := by
  simp only [term, Pi.smul_apply, smul_eq_mul, (F.irreducible j).degree_eq,
    signedDegree, Int.cast_mul, Int.cast_natCast]

omit [Finite G] in
public theorem signedDegree_ne_zero (j : Fin n) : F.signedDegree j ≠ 0 := by
  have hd : ((F.irreducible j).degree : ℤ) ≠ 0 := by
    exact_mod_cast (F.irreducible j).degree_pos.ne'
  rcases F.sign_eq j with h | h <;> simpa [signedDegree, h] using hd

private theorem sp_eq_cp (φ : ClassFunction G) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : scalarProduct G φ χ = characterProduct G φ χ := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  simp only [scalarProduct, characterProduct,
    Representation.representation_character_inv_eq_star_character]

public theorem term_orthonormal (j l : Fin n) :
    scalarProduct G (F.term j) (F.term l) = if j = l then 1 else 0 := by
  rw [term, term, scalarProduct_smul_left, scalarProduct_smul_right, star_intCast,
    sp_eq_cp _ (F.irreducible l)]
  by_cases h : j = l
  · subst l
    rw [irreducibleCharacter_self (F.irreducible j), if_pos rfl]
    rcases F.sign_eq j with hs | hs <;> norm_num [hs]
  · rw [irreducibleCharacters_orthogonal (F.irreducible j) (F.irreducible l)
      (fun he => h (F.injective he)), if_neg h]
    ring

public theorem one_scalarProduct_term (j : Fin n) :
    scalarProduct G 1 (F.term j) = 0 := by
  rw [term, scalarProduct_smul_right, sp_eq_cp _ (F.irreducible j),
    irreducibleCharacters_orthogonal isIrreducibleCharacter_one (F.irreducible j)
      (F.nonprincipal j).symm, zero_mul]

/-- Suzuki's summand for a signed irreducible, with its signed degree. -/
public theorem term_pairing (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (j : Fin n) :
    scalarProduct G (F.term j) (fun g => (Theory.Character.involutionPairCount g : ℂ)) =
      (Nat.card G : ℂ) / 147456 * (F.term j D.z ^ 2 / F.term j 1) := by
  rw [term, scalarProduct_smul_left,
    Theory.Character.scalarProduct_irreducible_involutionPairCount_of_fusion
      D.z D.z_order L.involution_fusion _ (F.irreducible j), D.centralizer_card]
  rcases F.sign_eq j with hs | hs <;>
    simp [hs] <;> ring
end SignedFamily
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

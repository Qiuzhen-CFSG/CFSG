module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.FirstThree.CaseOne
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.FirstThree.CaseTwo
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.Residual
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiPairings

/-!
# Compatibility of all constituents of the first three exceptional inductions

The signed Janko decomposition and the certified character calculations exclude
case (1) and prove zero products of the fourth and fifth multiplicities for
all six constituents in case (2). Orthogonality exhausts the support of the
three actual induced class functions. The principal character has zero fourth
multiplicity. This discharges exactly `FirstThreeCompatible`, the premise used
by `Existence.exists_irreducible_of_firstThreeCompatible`.

The theorem needs neither ambient simplicity nor the Sylow-three normalizer
order. The actual special induction data remain an explicit input; no degree-21
character, character table, group identification or permutation action is used.
Final degree-21 existence assembly remains in the parent Existence module.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.12–16,
DOI 10.1016/0021-8693(68)90002-1.
-/


namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CharacterOrder CharacterOrder.OrderExhaustion
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

private theorem scalar_orthogonal {φ ψ : ClassFunction G}
    (hφ : IsIrreducibleCharacter φ) (hψ : IsIrreducibleCharacter ψ) (hne : φ ≠ ψ) :
    scalarProduct G φ ψ = 0 := by
  have he : scalarProduct G φ ψ = characterProduct G φ ψ := by
    obtain ⟨n, ρ, _, rfl⟩ := hψ
    simp only [scalarProduct, characterProduct,
      Representation.representation_character_inv_eq_star_character]
  rw [he]
  exact irreducibleCharacters_orthogonal hφ hψ hne

/-- The first three exceptional inductions have no constituent with opposite
fourth and fifth multiplicities. This uses the actual Janko decompositions,
Sylow congruence and Suzuki pairings at order 443520. -/
public theorem firstThreeCompatible (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (hcard : Nat.card G = 443520)
    (I : SpecialInductionData D k) : FirstThreeCompatible I := by
  classical
  have hI := hasSuzukiPairings_of_localAnalysis D k L I
  obtain ⟨hu, hd⟩ := SignedAnalysis.unit_multiplicities_and_janko_decomposition D k L I hI
  rcases hd with ⟨F, h1, h2, h3⟩ | ⟨F, h1, h2, h3⟩
  · exact False.elim (FirstThree.caseOne_impossible D k L I hcard hI hu F h1 h2 h3)
  have hprod := FirstThree.caseTwo_products_zero D k L I hcard hI hu F h1 h2 h3
  intro χ hχ ⟨i, hi⟩
  by_cases hp : χ = 1
  · subst χ
    have hz : multiplicities I hχ 3 = 0 := by
      have hs := multiplicities_scalarProduct I hχ 3
      have hp3 : scalarProduct G (I.induced 3) 1 = exceptionalCoefficients 3 0 :=
        I.principal_multiplicity 3
      rw [hp3, show exceptionalCoefficients 3 0 = 0 from by decide +kernel] at hs
      exact_mod_cast hs.symm
    simp [hz]
  by_cases hf : ∃ j, F.character j = χ
  · obtain ⟨j, rfl⟩ := hf
    exact le_of_eq (hprod j).symm
  have hterms (j : Fin 6) : scalarProduct G (F.term j) χ = 0 := by
    rw [SignedFamily.term, scalarProduct_smul_left,
      scalar_orthogonal (F.irreducible j) hχ (fun he => hf ⟨j, he⟩), mul_zero]
  have hp' : scalarProduct G 1 χ = 0 :=
    scalar_orthogonal isIrreducibleCharacter_one hχ (Ne.symm hp)
  have hh0 := multiplicities_scalarProduct I hχ 0
  have hh1 := multiplicities_scalarProduct I hχ 1
  have hh2 := multiplicities_scalarProduct I hχ 2
  rw [h1] at hh0
  rw [h2] at hh1
  rw [h3] at hh2
  simp only [scalarProduct_add_left, scalarProduct_sub_left, hterms, hp',
    add_zero, sub_zero] at hh0 hh1 hh2
  apply False.elim
  apply hi
  fin_cases i
  · exact_mod_cast hh0.symm
  · exact_mod_cast hh1.symm
  · exact_mod_cast hh2.symm
end
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21

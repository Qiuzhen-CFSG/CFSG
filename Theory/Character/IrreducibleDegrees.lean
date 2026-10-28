module

public import Theory.Character.Divisibility

/-!
# Natural degrees and counting irreducible characters

The natural degree of an actual irreducible character is positive and divides
the group order. Over all irreducibles, the sum of its squares is the group
order, and the number of characters is the number of conjugacy classes.

These are natural-number interfaces to the representation-level divisibility
theorem and the complete-family orthogonality theorems. Reindexing a complete
family identifies its indices with the subtype of actual irreducible functions;
no character table or choice of a particular family enters the conclusions.
-/

noncomputable section
open scoped BigOperators

namespace IsIrreducibleCharacter

variable {G : Type*} [Group G] {χ : ClassFunction G}

/-- The dimension of an irreducible representation affording the character. -/
public def degree (hχ : IsIrreducibleCharacter χ) : ℕ := Classical.choose hχ

/-- The natural degree is the value at the identity. -/
public theorem degree_eq (hχ : IsIrreducibleCharacter χ) : χ 1 = (hχ.degree : ℂ) := by
  obtain ⟨ρ, _, hρ⟩ := Classical.choose_spec hχ
  simp [hρ, Representation.char_one, degree]

/-- An irreducible character has positive degree. -/
public theorem degree_pos (hχ : IsIrreducibleCharacter χ) : 0 < hχ.degree := by
  obtain ⟨ρ, hρ, _⟩ := Classical.choose_spec hχ
  let := hρ
  let := irreducible_nontrivial ρ
  have h := Module.finrank_pos (R := ℂ) (M := Fin (Classical.choose hχ) → ℂ)
  simpa [degree] using h

/-- An irreducible complex character's natural degree divides the group order. -/
public theorem degree_dvd_card [Finite G] (hχ : IsIrreducibleCharacter χ) :
    hχ.degree ∣ Nat.card G := by
  obtain ⟨ρ, hρ, _⟩ := Classical.choose_spec hχ
  let := hρ
  simpa [degree] using irreducible_dimension_dvd_group_order ρ

end IsIrreducibleCharacter

namespace Theory.Character

variable {G : Type*} [Group G] [Finite G]

private theorem ofConj_irreducible {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

private def completeFamilyEquiv {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    ι ≃ {θ : ClassFunction G // IsIrreducibleCharacter θ} :=
  Equiv.ofBijective (fun i => ⟨ofConjClassFunction (χ i), ofConj_irreducible (hχ.1 i)⟩) (by
    constructor
    · intro i j hij
      apply hχ.2.2
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      exact congrFun (congrArg Subtype.val hij) g
    · rintro ⟨θ, n, ρ, hρ, rfl⟩
      let := hρ
      obtain ⟨i, hi⟩ := hχ.2.1 (characterClassFunction ρ)
        ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
      exact ⟨i, Subtype.ext (by simp [hi, ofConjClassFunction_characterClassFunction])⟩)

/-- Count actual irreducible character functions by conjugacy classes. -/
public theorem card_irreducibleCharacters :
    Nat.card {χ : ClassFunction G // IsIrreducibleCharacter χ} =
      Nat.card (ConjClasses G) := by
  obtain ⟨ι, hι, χ, hχ, hc⟩ := card_irreducible_characters_eq_card_conjClasses (G := G)
  let := hι
  rw [← Nat.card_congr (completeFamilyEquiv hχ), Nat.card_eq_fintype_card, hc]

/-- The sum of squared natural degrees of all actual irreducibles is `|G|`. -/
public theorem sum_irreducibleCharacters_degree_sq
    [Fintype {χ : ClassFunction G // IsIrreducibleCharacter χ}] :
    ∑ χ : {χ : ClassFunction G // IsIrreducibleCharacter χ}, χ.property.degree ^ 2 =
      Nat.card G := by
  classical
  obtain ⟨ι, hι, χ, hχ, hs⟩ :=
    exists_completeIrreducibleCharacterFamily_sum_degree_normSq (G := G)
  let := hι
  let e := completeFamilyEquiv hχ
  have he (i : ι) : χ i (ConjClasses.mk (1 : G)) = ((e i).property.degree : ℂ) :=
    (e i).property.degree_eq
  have hs' : ∑ i : ι, (e i).property.degree ^ 2 = Nat.card G := by
    simp only [he, Complex.normSq_natCast, ← pow_two] at hs
    exact_mod_cast hs
  rw [← hs']
  exact (e.sum_comp (fun θ => θ.property.degree ^ 2)).symm

end Theory.Character

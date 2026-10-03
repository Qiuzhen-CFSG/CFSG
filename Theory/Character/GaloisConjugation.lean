module

public import Theory.Character.ClassFunction
public import Theory.Representation.SemilinearConjugation

/-!
# Galois conjugation of complex characters

A field automorphism acts on a representation by applying it to coordinates.
Semilinear conjugation transports invariant subspaces and applies the same
field automorphism to the trace. Consequently it preserves irreducible
characters and their degrees. This is the character-theoretic step in the
unique-degree rationality argument used in Wong (1964), Appendix (b), p. 109.
-/

public section

noncomputable section

variable {G : Type*} [Group G]

/-- An arbitrary field automorphism of `ℂ` preserves irreducible characters. -/
theorem IsIrreducibleCharacter.comp_ringEquiv {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (σ : ℂ ≃+* ℂ) :
    IsIrreducibleCharacter (fun g => σ (χ g)) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let e := Representation.coordinateSemilinearEquiv σ (Fin n)
  exact ⟨n, ρ.semilinearConjugate σ e,
    Representation.isIrreducible_semilinearConjugate σ ρ e hρ,
    funext (fun g => (Representation.character_semilinearConjugate σ ρ e g).symm)⟩

/-- Character degrees are fixed by every field automorphism of `ℂ`. -/
theorem IsIrreducibleCharacter.ringEquiv_degree {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (σ : ℂ ≃+* ℂ) : σ (χ 1) = χ 1 := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  rw [Representation.char_one]
  exact map_natCast σ _

/-- An irreducible character unique in its degree is fixed by every field automorphism. -/
theorem IsIrreducibleCharacter.fixed_of_unique_degree {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ)
    (hunique : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ 1 = χ 1 → θ = χ)
    (σ : ℂ ≃+* ℂ) (g : G) : σ (χ g) = χ g := by
  exact congrFun (hunique _ (hχ.comp_ringEquiv σ) (hχ.ringEquiv_degree σ)) g

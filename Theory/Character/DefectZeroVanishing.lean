module

public import Theory.Character.OrdinaryProjectorIdempotence
public import Theory.Character.IntegralIdempotentSupport

/-!
# Ordinary defect-zero character vanishing

An irreducible complex character whose degree is divisible by the order of a
Sylow `p`-subgroup vanishes on every element of order divisible by `p`.

The normalized character projector is a central idempotent. The Sylow index,
which is prime to `p`, clears its coefficient denominators. The integral
idempotent support theorem therefore kills its coefficient at `g⁻¹`; cancelling
the nonzero character degree gives the value at `g`.

Source: the ordinary defect-zero vanishing theorem used by Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)* (1967),
pp. 74–75. No block-membership or rational-realization hypothesis is needed.
-/

public section

namespace OrdinaryCharacter

variable {G : Type*} [Group G] [Finite G]

/-- An ordinary irreducible character of defect zero at `p` vanishes on all
`p`-singular elements. The degree and Sylow subgroup are supplied explicitly. -/
theorem value_eq_zero_of_sylow_card_dvd_degree {p n : ℕ} [Fact p.Prime]
    (P : Sylow p G) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hdegree : χ 1 = (n : ℂ)) (hdiv : Nat.card P ∣ n)
    (g : G) (hg : p ∣ orderOf g) : χ g = 0 := by
  obtain ⟨d, ρ, hρ, rfl⟩ := hχ
  let := hρ
  have hnonzero : ρ.character 1 ≠ 0 := by
    let := irreducible_nontrivial ρ
    rw [Representation.char_one]
    exact Nat.cast_ne_zero.mpr
      (Module.finrank_pos_iff.mpr (inferInstance : Nontrivial (Fin d → ℂ))).ne'
  apply value_eq_zero_of_projector_coeff_inv_eq_zero hnonzero g
  exact IntegralIdempotentSupport.coeff_eq_zero_of_prime_dvd_orderOf p
    (projector ρ.character) (projector_isIdempotent ⟨d, ρ, hρ, rfl⟩)
    (projector_mem_center ρ.char_conj)
    (projector_coeff_integralAway P ⟨d, ρ, rfl⟩ hdegree hdiv)
    g⁻¹ (by simpa only [orderOf_inv] using hg)

end OrdinaryCharacter

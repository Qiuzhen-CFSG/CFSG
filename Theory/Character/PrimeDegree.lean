module

public import Theory.Character.SimpleCriteria
public import Theory.Character.SimpleFaithful
public import Theory.Character.DefectZeroVanishing

/-!
# Faithfulness and vanishing for prime-degree characters

A rational-valued irreducible character of prime degree in a finite simple
group is afforded by a faithful complex representation with the same rational
values. When the corresponding Sylow subgroup has that prime order, the
character has defect zero and vanishes on every prime-singular element.

These statements use characters on conjugacy classes, as in the ABG
principal-character data. They do not assume a rational realization.

Source: Alperin--Brauer--Gorenstein, III.8 Lemma 4 and Proposition 5,
article pp.116--117; the general defect-zero theorem is proved in
`Theory.Character.DefectZeroVanishing`.
-/

namespace IsIrreducibleConjCharacter
variable {G : Type*} [Group G] [Finite G] {χ : ConjClassFunction G}

private theorem ordinary (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

/-- Rationality is retained on a faithful complex representation affording
the given prime-degree character of a simple group. -/
public theorem exists_faithful_rational_prime_degree [IsSimpleGroup G]
    (hχ : IsIrreducibleConjCharacter χ) {p : ℕ} (hp : p.Prime)
    (hd : χ (ConjClasses.mk 1) = (p : ℂ))
    (hrat : ∀ g : G, ∃ q : ℚ, χ (ConjClasses.mk g) = (q : ℂ)) :
    ∃ ρ : Representation ℂ G (Fin p → ℂ),
      ofConjClassFunction χ = ρ.character ∧ Function.Injective ρ ∧
        (∀ g : G, ∃ q : ℚ, ρ.character g = (q : ℂ)) := by
  obtain ⟨n, ρ, hρ, he⟩ := ordinary hχ
  have hn : n = p := by
    have heval := congrFun he 1
    rw [ofConjClassFunction_apply, hd, Representation.char_one] at heval
    simpa using (Nat.cast_injective heval).symm
  subst n
  let := hρ
  refine ⟨ρ, he, ρ.injective_of_isSimpleGroup_of_one_lt_finrank
    (by simpa using hp.one_lt), ?_⟩
  intro g
  rw [← he]
  exact hrat g

/-- An irreducible character of degree `p` vanishes on `p`-singular elements
when a Sylow `p`-subgroup has order `p`. -/
public theorem prime_degree_vanishing (hχ : IsIrreducibleConjCharacter χ)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : Nat.card P = p)
    (hd : χ (ConjClasses.mk 1) = (p : ℂ)) (g : G) (hg : p ∣ orderOf g) :
    χ (ConjClasses.mk g) = 0 := by
  exact OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P (ordinary hχ)
    hd (by rw [hP]) g hg

end IsIrreducibleConjCharacter

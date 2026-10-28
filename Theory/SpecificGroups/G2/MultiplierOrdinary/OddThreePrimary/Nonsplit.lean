module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.LocalData
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit.Descent

/-!
# The nonsplit G₂ Sylow-three normalizer configuration

An explicit quaternion matrix solves the longest-Weyl Frobenius equation.
Conjugating the norm-one torus by that solution makes it rational; the same
conjugation makes its Weyl cycle, swapping reflection, and central inverter
rational. Fixed-point descent places all witnesses in the literal split-octonion
automorphism group over F. The torus index calculation then constructs a full
Sylow three-subgroup for every three-adic valuation of p+1.

This supplies the nonsplit local input of the ordinary G₂ multiplier
calculation, with no covering, recognition, or geometric premise. The
central-cover argument and final universal-kernel assembly remain in
`OddThreePrimary`.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The octonion model, Weyl maps, and order formula are attributed ATLAS ports;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary
variable {F : Type*} [Field F] [Finite F]

/-- The actual nonsplit torus and its rational Weyl elements provide every
field of the Sylow-three normalizer configuration in the source prime-field range. -/
theorem exists_nonsplit_localData {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) (hd : 3 ∣ p+1) : Nonempty (LocalData F) := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using hF)
  obtain ⟨u,hu⟩ := Nonsplit.exists_longestWeyl_lang hF hp
  exact Nonsplit.exists_localData_of_lang hF hd u hu
end Atlas.G2.MultiplierOrdinary.OddThreePrimary
end

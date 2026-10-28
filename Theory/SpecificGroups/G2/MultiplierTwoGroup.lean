module

public import Theory.SpecificGroups.G2.MultiplierFourTwoGroup
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining

/-!
# Two-primary universal kernels for higher binary G₂ groups

For every finite field of order 2^m with m > 1, the canonical universal
cover of the octonion G₂ model has a two-group kernel. At order four this
uses the exceptional odd-primary exclusions; at larger orders it uses the
complete nondefining-prime calculation. No defining-prime calculation or
triviality of the exceptional covering kernel is needed.

This is the precise multiplier property needed to lift two-core information
through a marked G₂ action. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, I.1.1–I.1.4, printed pp.407–408. The imported octonion model
and local calculations retain their ATLAS attribution (LICENSES/ATLAS.txt).
-/

public section

namespace Atlas.G2.FiniteCover

variable {F : Type*} [Field F] [Finite F]

/-- Uniform two-primary control, including the exceptional field of order four,
for the literal canonical universal projection. -/
theorem universalKernel_isPGroup_of_card_pow {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m) : IsPGroup 2 (Kernel F) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hm
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  by_cases h4 : Nat.card F = 4
  · exact MultiplierFourBound.universalKernel_isPGroup_of_card_four h4
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    exact MultiplierOrdinary.Nondefining.universalKernel_isPGroup (by omega)

end Atlas.G2.FiniteCover

end

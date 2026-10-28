module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!+# The G₂ Cartan action with automorphism coverage discharged

The raw A.3.15(5) configuration supplies the actual octonion model over a field
of order 2ⁿ, n > 1. These numerical hypotheses give finiteness, characteristic
two and field order greater than two, so the concrete inner–field coverage
theorem applies. The existing raw Cartan argument supplies simultaneous
Sylow/torus alignment and places the inner factor in the Borel. Its kernel
calculation then leaves a uniform Frobenius power on B and on B/Φ(B).

Neither theorem below retains an automorphism-coverage, alignment or power-action
premise. The supplied raw configuration includes every field/Cartan clause;
its existence is the earlier A.3.15 input to this action step.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5), printed
pp.50–51, and Proposition 1.3.4, printed p.511 (`refs/quasithin.pdf`).
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source

private theorem coverage_of_binary_card {E : Type*} [Field E] {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) (hn : 1 < n) :
    Function.Surjective (semilinearAction (F := E)) := by
  let : Finite E := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (by decide))
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))))
  have hq : 2 < Nat.card E := by
    rw [hcard]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  exact semilinearAction_surjective hq

variable {J E : Type*} [Group J] [Finite J] [Field E]
    (D : Subgroup J) [D.Normal] {κ : GroupClass} {e : D ≃* Model E}
    {S : Sylow 2 J} {B : Subgroup J} {p n f : ℕ}
    {F H I : Subgroup (MulAut D)}

/-- Each actual normalizer element acts on B by one Frobenius power, from the
full source configuration with concrete automorphism coverage discharged. -/
theorem normalizer_conjugation_power_of_source
    (h : RawCartan.Input D κ e S B p n f F H I) :
    ∀ s : ↥((S : Subgroup J) ⊓ normalizer B), ∃ k : ℕ, ∀ b : B,
      (s : J) * (b : J) * (s : J)⁻¹ = (b : J) ^ (2 ^ k) :=
  normalizer_conjugation_power_of_raw_cartan D h
    (coverage_of_binary_card h.field_card h.exponent_large)

/-- The G₂ action step in Proposition 1.3.4, on the literal Frattini quotient
and actual N_S(B), with no remaining coverage or alignment hypothesis. -/
theorem frattini_power_of_source
    (h : RawCartan.Input D κ e S B p n f F H I) :
    ∀ (s : ↥((S : Subgroup J) ⊓ normalizer B)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v :=
  frattini_power_of_raw_cartan D h
    (coverage_of_binary_card h.field_card h.exponent_large)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source

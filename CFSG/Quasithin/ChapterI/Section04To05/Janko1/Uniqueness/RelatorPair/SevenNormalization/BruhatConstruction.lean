module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.BruhatConstruction.Inverter
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure

/-!
# Assembly of Janko's local Bruhat configuration

The odd-prime centralizer structure and the supplied group order construct
the marked normalizer, its inverting involution, and the fifth-power
identity. Every subgroup and conjugation is in the original group G.

The source theorem discharges OddPrimeCentralizerStructure h using the
proved cyclic-complement alternatives and exceptional order-27 exclusion.
Thus it constructs the full configuration from the original local hypotheses
and the supplied order. The explicit fusion premise in the source contract
is already proved from simplicity by Order.Fusion and is not needed again.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, equation (6.2),
describing Janko, J. Algebra 3 (1966), 147–186. This proves the local
configuration from the source hypotheses, with no representation,
recognition, generation, or assumed configuration.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Construct the complete Bruhat configuration from the independently
produced odd-prime centralizer decomposition and the supplied source order.
The structural premise must be discharged by the source assembly. -/
public theorem exists_bruhatFrame_of_centralizerStructure
    (h : Janko1CentralizerData G)
    (s : Janko1CentralizerData.OddPrimeCentralizerStructure h)
    (horder : Nat.card G = 175560) : Nonempty (BruhatFrame h) := by
  obtain ⟨D⟩ := exists_normalizerFrame_of_source h
  obtain ⟨w, hw, hcomm, hinv⟩ := D.exists_inverter h s horder
  exact exists_bruhatFrame_of_inverter D w hw hcomm hinv
    (ambient_prime_centralizer_card_dvd h s 3 (Or.inl rfl) D.u D.order_u)

/-- Janko's local configuration preceding the matrix normalization, including
the structure identity `(x * w)^5 = 1`. The odd-prime centralizer structure
is proved from the local data and simplicity, so no configuration or
centralizer-decomposition premise remains. -/
public theorem exists_bruhatFrame_of_source
    (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (_hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    Nonempty (BruhatFrame h) :=
  exists_bruhatFrame_of_centralizerStructure h h.oddPrimeCentralizerStructure horder

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization

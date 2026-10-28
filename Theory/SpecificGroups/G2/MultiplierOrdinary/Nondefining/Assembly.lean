module

public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining

/-!
# Applying the even-characteristic nondefining calculation

The full odd-prime exclusion discharges the nondefining-prime premise of the
existing ordinary-multiplier assembly for the literal canonical projection.
Only the independent multiplication law on its positive-root sections remains
an input. This conditional application does not assert that law or the full
trivial-multiplier entry of Aschbacher–Smith I.1.3–I.1.4, pp.407–408.
-/

public section

namespace Atlas.G2.MultiplierOrdinary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The ordinary even-field kernel vanishes once the defining-prime root
relations are proved; every nondefining-prime premise is discharged. -/
theorem even_universalProjection_ker_eq_bot_of_positive_relations
    (hF : 4 < Nat.card F)
    (L : RootSections (universalProjection (Model F))) (hL : L.ProductCompatible) :
    (universalProjection (Model F)).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_positive_relations (p := 2) (by omega) L hL
    (fun _ hr hr2 => Nondefining.not_dvd_card_universal_kernel hF hr hr2)

end Atlas.G2.MultiplierOrdinary

end

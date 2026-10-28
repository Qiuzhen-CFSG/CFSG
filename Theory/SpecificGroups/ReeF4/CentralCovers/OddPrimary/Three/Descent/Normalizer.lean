module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer.Descent
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer.Counting
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order

/-!
# The actual three-primary local geometry of every positive-parameter Ree group

The marked exceptional torus, its literal coordinate cycle and transposition,
and the opposition inverter give the complete three-primary configuration.
The proved carrier order makes the torus-by-cycle subgroup Sylow. Every
normalizer element descends through the same Lang solution as the torus;
no monomial realization or unitary embedding is an input.

The final application excludes three from the kernel of the original perfect
central covering map. This discharges the three-primary geometric premise
in `OddPrimary.not_dvd_kernel_of_geometry`.
Sources: GLS3 Example 2.6.3, Table 4.7.3A and §6.1; Aschbacher--Smith I.1.1--4.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent
open ExceptionalTorus Normalizer

/-- The complete original three-primary geometry, for all m ≥ 1. -/
theorem nonempty_threeSylowData (m : ℕ) (hm : 1 ≤ m) : Nonempty (ThreeSylowData m) :=
  threeSylowData_of_torus_actions m (Order.card_model m)
    (modelMap m hm) (modelMap_injective m hm)
    (modelCycle m hm) (modelSwap m hm) (modelInverter m hm)
    (modelCycle_cube m hm) (modelCycle_torus m hm) (modelSwap_torus m hm)
    (modelInverter_torus m hm) (modelInverter_cycle m hm)

/-- Actual perfect-central-cover consumer, with every geometric premise discharged. -/
theorem not_three_dvd_kernel (m : ℕ) (hm : 1 ≤ m) {E : Type*} [Group E] [Finite E]
    (c : PerfectCentralCovering.Cover E (Model m)) : ¬ 3 ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨D⟩ := nonempty_threeSylowData m hm
  exact D.not_three_dvd_kernel c

end ReeF4.CentralCovers.OddPrimary.Three.Descent

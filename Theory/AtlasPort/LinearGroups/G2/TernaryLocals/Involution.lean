module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Generators
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Order
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core
public import Theory.Quasithin.EvenCharacteristic

/-!
# Assembly of the ternary involution local calculation

The octonion frame injection gives the unconditional bound `card_le` on the
actual involution centralizer. The shared `Generators` module constructs five
root/torus elements in it and verifies their local quaternion and cubic
relations. The `Order` calculation exhibits 576 distinct root/torus words,
so these generators give the whole centralizer and its order is exactly 576.
The `Core` calculation constructs a normal quaternion two-subgroup and checks
its centralizer in the faithful octonion coordinates. Its intrinsic two-core
condition transports to the full centralizer along the generation equality.

The final theorems `card`, `generated_eq_top`, and `centralizer_pCore` discharge
both calculations. They have no additional hypotheses on the concrete model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Main
Theorem 0.1.2(4), printed pp.3–4, repeated on pp.481–482; I.4(G1), p.417.
The coordinate calculations use the licensed ATLAS split-octonion port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.TernaryLocals.Involution

/-- A matching order for the explicitly generated subgroup gives the full local order. -/
theorem card_of_generated_card (hcard : Nat.card generated = 576) : Nat.card P = 576 := by
  apply Nat.le_antisymm card_le
  rw [← hcard]
  exact generated.card_le_card_group

/-- The frame bound turns the root-subgroup order into a generation theorem. -/
theorem generated_eq_top_of_card (hcard : Nat.card generated = 576) : generated = ⊤ := by
  apply Subgroup.eq_top_of_le_card
  rw [hcard]
  exact card_le

/-- Conditional assembly; both the root-subgroup order and its intrinsic core
centralizer must still be supplied. -/
theorem centralizer_pCore_of_generated
    (hcard : Nat.card generated = 576)
    (hcore : Subgroup.centralizer (pCore 2 generated : Set generated) ≤ pCore 2 generated) :
    Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  let e : generated ≃* P :=
    (MulEquiv.subgroupCongr (generated_eq_top_of_card hcard)).trans Subgroup.topEquiv
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hcore

/-- The actual involution centralizer in the ternary octonion group has order 576. -/
theorem card : Nat.card P = 576 :=
  card_of_generated_card card_generated

/-- The five concrete root and torus elements generate the whole involution centralizer. -/
theorem generated_eq_top : generated = ⊤ :=
  generated_eq_top_of_card card_generated

/-- The intrinsic two-core of the actual involution centralizer is self-centralizing. -/
theorem centralizer_pCore : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P :=
  centralizer_pCore_of_generated card_generated generated_centralizer_pCore

end Atlas.G2.TernaryLocals.Involution

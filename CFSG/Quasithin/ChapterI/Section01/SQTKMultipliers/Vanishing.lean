module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Statement
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Symplectic
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# Completed vanishing families in the I.1.3 catalogue

The characteristic-two four-space symplectic groups, PSL₅(2), and ordinary
G₂ models have trivial canonical multiplier. These source applications
transport the actual universal kernel along the model isomorphism; no
conclusion is inferred from omission from a printed table.

Source: Aschbacher--Smith I.1.3, printed p.407, and GLS3 §6.1. The exceptional
G₂(4) and the derived G₂(2) endpoint are deliberately separate calculations.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering Theory.GroupTheory
universe u
variable {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]

/-- Every characteristic-two PSp₄ model in the simple range has trivial multiplier. -/
theorem multiplier_psp4_even {n : ℕ} (hn : 1 < n)
    (hS : ClassicalGroup.IsPSp S 2 (2 ^ n)) : Subsingleton (schurMultiplier S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hlarge : 3 < Nat.card F := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ n by omega)
    omega
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let k : schurMultiplier S ≃* (PUnit : Type) := (schurMultiplierCongr e).trans
    (LieMultipliers.Symplectic.evenProjectiveUniversalKernelEquivPUnit F hlarge)
  exact k.injective.subsingleton

/-- The literal PSL₅(2) matrix-model branch has trivial canonical multiplier. -/
theorem multiplier_psl5_two (hS : ClassicalGroup.IsPSL S 5 2) :
    Subsingleton (schurMultiplier S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple F
  let k : schurMultiplier S ≃* (PUnit : Type) := (schurMultiplierCongr e).trans
    (LieMultipliers.Symplectic.psl5TwoUniversalKernelEquivPUnit F hcard)
  exact k.injective.subsingleton

/-- Ordinary binary G₂ models vanish above the exceptional field order four. -/
theorem multiplier_g2_even {n : ℕ} (hn : 3 ≤ n)
    (hS : ClassificationModels.IsG2At S (2 ^ n)) : Subsingleton (schurMultiplier S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let : Fact (2 < Nat.card F) := ⟨by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    omega⟩
  let : Subsingleton (schurMultiplier (Atlas.G2.Model F)) := by
    change Subsingleton (PerfectCentralCovering.universalProjection (Atlas.G2.Model F)).ker
    rw [Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow hcard hn]
    infer_instance
  exact (schurMultiplierCongr e).injective.subsingleton

/-- The odd prime G₂ family has trivial canonical multiplier for p > 3. -/
theorem multiplier_g2_odd_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hS : ClassificationModels.IsG2At S p) : Subsingleton (schurMultiplier S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let : Subsingleton (schurMultiplier (Atlas.G2.Model F)) := by
    change Subsingleton (PerfectCentralCovering.universalProjection (Atlas.G2.Model F)).ker
    rw [Atlas.G2.MultiplierOrdinary.prime_universalProjection_ker_eq_bot hcard hp3]
    infer_instance
  exact (schurMultiplierCongr e).injective.subsingleton

end CFSG.Quasithin.ChapterI.SQTKMultipliers

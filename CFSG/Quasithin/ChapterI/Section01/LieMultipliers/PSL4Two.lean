module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier

/-!
# The L₄(2) source multiplier row

The source's projective-model witness specifies a two-element field and an
actual group isomorphism. The proved binary degree-four calculation therefore
identifies the kernel of the original group's constructed universal cover
with C₂. No other higher classical family or cohomology calculation is used.

Source: Aschbacher–Smith, I.1.3(1), printed p.407. The remaining multiplier
rows and the exhaustive source table belong to the I.1 assembly.
-/

public section

namespace CFSG.Quasithin.ChapterI.LieMultipliers.PSL4Two

open PerfectCentralCovering

universe u

/-- The L₄(2) clause of I.1.3(1), on the source's actual projective model. -/
theorem schurMultiplier_equiv_two
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (hS : ClassicalGroup.IsPSL S 4 2) :
    Nonempty (schurMultiplier S ≃* Multiplicative (ZMod 2)) := by
  rcases hS with ⟨F, hField, hFinite, hF, ⟨e⟩⟩
  let := hField
  let := hFinite
  exact ⟨Matrix.PSL4Two.schurMultiplierEquivTwo F hF e⟩

/-- The order consequence of the full multiplier isomorphism. -/
theorem schurMultiplier_card
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (hS : ClassicalGroup.IsPSL S 4 2) :
    Nat.card (schurMultiplier S) = 2 := by
  obtain ⟨e⟩ := schurMultiplier_equiv_two hS
  simpa using Nat.card_congr e.toEquiv

end CFSG.Quasithin.ChapterI.LieMultipliers.PSL4Two

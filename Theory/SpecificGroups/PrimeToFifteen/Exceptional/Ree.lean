module
public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Three-divisibility for the concrete Ree carriers

The small Ree root subgroup has cardinality q cubed and embeds in the actual
matrix group. For the large Ree carrier the constructed exceptional endomorphism
supplies the local input used by the existing cubic-element calculation.
These results have no simplicity or order-formula premise.

Sources: GLS3 Sections 2.2 and 2.6; the attributed small Ree root-matrix
construction in the imported ATLAS modules.
-/
public section
namespace Atlas.ReeG2

theorem three_dvd_card_model (F : Type*) [Field F] [Finite F] [CharP F 3]
    (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) : 3 ∣ Nat.card (Model F m) := by
  have hroot : 3 ∣ Nat.card (rootSubgroup m hcard) := by
    rw [card_rootSubgroup, hcard, ← pow_mul]
    exact dvd_pow_self 3 (by omega)
  exact hroot.trans (Subgroup.card_dvd_of_le (rootSubgroup_le_generated m hcard))
end Atlas.ReeG2

namespace ReeF4

theorem three_dvd_card_model (m : ℕ) : 3 ∣ Nat.card (Model m) := by
  rw [← Nat.card_congr (canonicalLocalBlockInput m).modelEquiv.toEquiv]
  exact (canonicalLocalBlockInput m).three_dvd_card

end ReeF4

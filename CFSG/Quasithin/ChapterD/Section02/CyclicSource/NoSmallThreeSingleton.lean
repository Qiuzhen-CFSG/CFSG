module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFamily
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFourSpace
/-!
# The singleton cubic-support endpoint

When the literal source family Y has one member, D.2.26 makes its
four-dimensional support the whole module. The four-space endpoint then
supplies the required original local-generation witness.
Source: Aschbacher–Smith D.2.27, p.191.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The singleton-family case of D.2.27, on the literal source family Y. -/
theorem Hypotheses.singleton_fourSpaceThreeFactors_localGeneration (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (D : Subgroup G) (hY : fourSpaceThreeFactors ρ = {D}) : Nonempty (LocalGeneration ρ) := by
  have hD : D ∈ fourSpaceThreeFactors ρ := by rw [hY]; exact Set.mem_singleton D
  have hm := h.fourSpaceThreeFactors_moved_eq_top hq hfive hNo
  rw [hY,sSup_singleton] at hm
  have hd := hD.2.2
  rw [hm,finrank_top] at hd
  exact h.finrank_four_localGeneration hq hfive hNo hd

end CFSG.Quasithin.ChapterD.CyclicSource

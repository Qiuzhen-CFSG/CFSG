module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Output models for the end-node parabolic

The two end nodes of the A₃ diagram generate the maximal parabolic
stabilizing a two-dimensional subspace in the natural four-dimensional
binary space. Its inverse image in L must be specified under an actual
isomorphism from L/O₂(L). An eight-letter star marking must likewise
intertwine the given action, allowing a relabelling of the letters.

These structures specify outputs to be constructed. They assume neither
their existence nor the centralizer or maximality assertions of 15.3.32.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(4), printed pp.1132–1133.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

variable {G : Type*} [Group G]

/-- The actual inverse image of an end-node parabolic, without a family tag
or an assumed maximality conclusion. -/
structure EndNodeParabolicModel (L K : Subgroup G) where
  le_component : K ≤ L
  quotient : (L ⧸ pCore 2 L) ≃* BinaryLinear.GL (Fin 4 → ZMod 2)
  plane : Submodule (ZMod 2) (Fin 4 → ZMod 2)
  dimension : Module.finrank (ZMod 2) plane = 2
  preimage : (BinaryLinear.parabolic plane).comap
    (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = K.subgroupOf L

/-- Compatibility uses the original star quotient and the actual permutation
action, with only a relabelling of its eight letters. -/
structure CompatibleStarMarking (d : LocalData G) (I U : Subgroup G)
    (a : NaturalEightAction I U) where
  equiv : d.Star I ≃* Equiv.Perm (Fin 8)
  relabel : Equiv.Perm (Fin 8)
  compatible : ∀ i : I,
    equiv (d.starMap I i) = relabel * a.actor i * relabel⁻¹

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end

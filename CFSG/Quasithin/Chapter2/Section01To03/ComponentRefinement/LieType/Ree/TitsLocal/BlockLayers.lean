module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.Obstructions

/-!
# The Tits second-parabolic block calculation in coordinate sections

The intrinsic actor calculation excludes short subnormal subgroups in any
normal coordinate domain with two-group quotient, surjective coordinates
onto the second Tits parabolic, surjective maps on the two-cores, and a
two-group common kernel. The general CoreSection argument is reused from
its existing G2 namespace; its theorem is independent of the G2 model.

The `BlockLayers.ComponentOrbit` extension constructs the coordinate section
from the commuting component orbit. The `BlockLayers.Local` extension then
discharges the section premise and proves the local block obstruction in
Aschbacher–Smith 2.3.9(7), printed p.526. Adjoining the ambient Sylow subgroup
may permute components; no step assumes that it fixes L.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

open Subgroup ChapterC

/-- The group-structural input: actual surjective coordinates onto
the marked second parabolic, with their two-core images and common kernel. -/
abbrev TitsSecondCoreSection (K : Type*) [Group K] :=
  G2.RelativeBlocks.CoreSection K Tits.ExceptionalParabolics.second

/-- The proved intrinsic actor calculation and relative subnormal core-action
lemma exclude shortness once the component-orbit section is constructed. -/
theorem tits_not_short_of_secondCoreSection {K : Type*} [Group K] [Finite K]
    (d : TitsSecondCoreSection K) (B : Subgroup K) (hs : B.IsSubnormal) :
    ¬ IsShort B := by
  apply G2.RelativeBlocks.not_short_of_coreSection d ?_ B hs
  intro X _ hp hsquare
  exact Tits.RelativeSecondBlockLayers.eq_bot_of_core_square X hp hsquare

/-- This is the original layer-obstruction interface, conditional only on the
structural section. It follows because no relative block can exist there. -/
theorem tits_layers_of_secondCoreSection {K : Type*} [Group K]
    (d : TitsSecondCoreSection K) (B : Subgroup K) (hb : IsBlock B) :
    HasNoncentralTwoLayer B := by
  let : Finite K := hb.finite
  exact (tits_not_short_of_secondCoreSection d B hb.subnormal hb.short).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end

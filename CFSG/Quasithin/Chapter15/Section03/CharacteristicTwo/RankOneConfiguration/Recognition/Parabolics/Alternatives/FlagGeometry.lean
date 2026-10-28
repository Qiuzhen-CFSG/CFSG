module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces

/-!
# The Lie geometry carried by the eight-point marking

Restrict the actual star-quotient equivalence to its marked A₈ component,
then compose with the simultaneous exceptional comparison. This single
linear equivalence sends the component intersection to the middle minimal
parabolic and the component Sylow intersection to the full Lie flag.
It also sends any marked end-node subgroup to the corresponding cut
stabilizer. Thus the permutation and Lie markings refer to the same
subgroups, including the even part of the pair stabilizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.28(3) and 15.3.32(4), printed pp.1131–1133 (PDF pp.1148–1150).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
variable {G : Type*} [Group G] {d : LocalData G} {I L : Subgroup G}

namespace MiddleNodeFlagMarking

/-- The restriction of the specified eight-point action to its actual component. -/
noncomputable def componentEquiv (m : MiddleNodeFlagMarking d I L) :
    d.starImage I L ≃* alternatingGroup (Fin 8) :=
  (m.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr m.component)

/-- The linear interpretation of that same component action. -/
noncomputable def linear (m : MiddleNodeFlagMarking d I L) :
    d.starImage I L ≃* LinearGroup 4 :=
  m.componentEquiv.trans m.comparison.equiv

private theorem map_componentSubgroup (m : MiddleNodeFlagMarking d I L)
    (X : Subgroup (d.Star I)) :
    (X.subgroupOf (d.starImage I L)).map m.componentEquiv.toMonoidHom =
      (X.map m.equiv.toMonoidHom).subgroupOf (alternatingGroup (Fin 8)) := by
  apply map_injective (alternatingGroup (Fin 8)).subtype_injective
  rw [map_map, subgroupOf_map_subtype]
  have he : (alternatingGroup (Fin 8)).subtype.comp m.componentEquiv.toMonoidHom =
      m.equiv.toMonoidHom.comp (d.starImage I L).subtype := rfl
  rw [he, ← map_map, subgroupOf_map_subtype, map_inf _ _ _ m.equiv.injective,
    m.component]

/-- The component intersection is the middle-node minimal Lie parabolic. -/
theorem linear_intersection (m : MiddleNodeFlagMarking d I L) :
    ((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map
      m.linear.toMonoidHom = minimalParabolic m.comparison.basis 1 := by
  change ((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map
    (m.comparison.equiv.toMonoidHom.comp m.componentEquiv.toMonoidHom) = _
  rw [← map_map, map_componentSubgroup, m.component_intersection,
    inf_subgroupOf_right]
  exact m.comparison.middle

/-- The actual component Sylow image is the Borel for the same Lie flag. -/
theorem linear_sylow (m : MiddleNodeFlagMarking d I L) :
    ((d.starImage I d.S).subgroupOf (d.starImage I L)).map
      m.linear.toMonoidHom = cutStabilizer m.comparison.basis Set.univ := by
  change ((d.starImage I d.S).subgroupOf (d.starImage I L)).map
    (m.comparison.equiv.toMonoidHom.comp m.componentEquiv.toMonoidHom) = _
  rw [← map_map, map_componentSubgroup, m.sylow]
  exact m.comparison.borel

/-- An end-node marking uses the same exceptional equivalence and basis. -/
theorem linear_end (m : MiddleNodeFlagMarking d I L)
    (X : Subgroup (d.Star I))
    (hX : X.map m.equiv.toMonoidHom = fourStabilizer ⊓ alternatingGroup (Fin 8)) :
    (X.subgroupOf (d.starImage I L)).map m.linear.toMonoidHom =
      cutStabilizer m.comparison.basis {1} := by
  change (X.subgroupOf (d.starImage I L)).map
    (m.comparison.equiv.toMonoidHom.comp m.componentEquiv.toMonoidHom) = _
  rw [← map_map, map_componentSubgroup, hX, inf_subgroupOf_right]
  exact m.comparison.ends

end MiddleNodeFlagMarking
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics

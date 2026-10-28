module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Plane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Transport

/-!
# Attach the actual V₂ marking to a containing constituent

The source four-group has no Y₊-fixed vector. Since Y₊ ≤ L, its
intersection with the L-fixed space is also zero. The actual normalizer
calculation then supplies the exact parabolic stabilizer after restriction
to any containing Irr+ constituent, and the central quotient stays injective
on the line. The containing constituent remains an explicit hypothesis:
this is the assembly step, not the missing B.5.6 comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.26–29 and the first paragraph of 15.3.31, pp.1130–1132.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hf : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

theorem plane_disjoint_component_fixed (hline : LineData d I) (hYL : d.Yplus ≤ c.L) :
    Disjoint (planeSpace d c)
      (fixedSpace (componentAction d c hn hI hf P hP) (d.starImage I c.L)) := by
  apply (hline.planeSpace_fixed_disjoint d c hn hI hf P hP).mono_right
  intro v hv y
  exact hv ⟨y, (Subgroup.map_mono (Subgroup.comap_mono hYL)) y.property⟩

/-- Conditional assembly: select a containing Irr+ member first. The local
source data then supplies its exact marked line and faithful central projection. -/
theorem marked_of_containing_constituent (hline : LineData d I)
    (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (W : Submodule (ZMod 2) (Additive ((d.componentModule I c.L).subgroupOf I)))
    (hW : IsIrrPlus (componentAction d c hn hI hf P hP) (d.starImage I c.L) W)
    (hEW : planeSpace d c ≤ W) :
    Nonempty (MarkedConstituent (componentAction d c hn hI hf P hP)
      (d.starImage I c.L) (planeSpace d c)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L))) :=
  markedConstituent_of_containment _ _ _ W _
    (hline.planeSpace_card d c P hP hYL)
    (plane_stabilizer_eq_of_rank_one d c hn hI hf P hP hline hYL hRank hYRank)
    (plane_disjoint_component_fixed d c hn hI hf P hP hline hYL) hW hEW

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents

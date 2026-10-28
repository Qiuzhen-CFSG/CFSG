module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralResidualImage
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.CyclicWreathExclusion

/-!
# The marked cubic dihedral branch of original15.2.4

The original residual image in the three-marked dihedral row has order three.
The chosen cyclic centralizer-rank theorem therefore applies directly, and
the literal H-star intersection cannot come from an S5 wreath C2 quotient.
The five-marked row remains the separate later source argument.

Source: Aschbacher--Smith15.2.3(1)(i)--4, printed pp.1105--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The actual cubic dihedral source branch excludes the symmetric-five wreath local. -/
theorem source_dihedral_cubic_HStar_not_symmetricFive_wreath
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 3 m) (hd : DihedralMarking l 3 m)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  have he := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  have hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3 := by
    exact (congrArg (fun K : Subgroup (internalActionImage M V hV.normalized) => Nat.card K) he).trans
      ((card_map_of_injective (Jhat (imageRepresentation M V hV.normalized)).subtype_injective).trans
        hd.card_kernel)
  exact source_chosen_cubic_HStar_not_symmetricFive_wreath hG T hM hJ hu hV hc hH

end CFSG.Quasithin.Chapter15.Section02

module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Transport
public import Theory.Representation.ExtraspecialBinarySix.FixedPlanes

/-!
# Fixed and moved planes on the actual extraspecial source image

The faithful degree-six calculation is applied to the original two-residual
and its noncentral cubic subgroup. No Sylow or component choice is added.
Source: Aschbacher--Smith, Notation 15.1.16(c), printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The source extraspecial action supplies both dimensions and the direct sum. -/
theorem source_image_planes
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (X : Subgroup (pResidual 2 (internalActionImage M V hn)))
    (hX : Nat.card X = 3) (hXZ : X ≠ center (pResidual 2 (internalActionImage M V hn))) :
    let A := X.map (pResidual 2 (internalActionImage M V hn)).subtype
    Module.finrank (ZMod 2) (fixedSpace (imageRepresentation M V hn) A) = 2 ∧
    Module.finrank (ZMod 2) (subspaceCommutator (imageRepresentation M V hn) ⊤ A) = 4 ∧
    IsCompl (fixedSpace (imageRepresentation M V hn) A)
      (subspaceCommutator (imageRepresentation M V hn) ⊤ A) := by
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  exact ExtraspecialBinarySix.noncentral_cubic_planes (imageRepresentation M V hn)
    (imageRepresentation_injective M V hn) _ hcard hdim X hX hXZ

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

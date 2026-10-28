module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.SourceElementary

/-!
# The original FSU elementary conjugate-span alternative

For either original actor case, the actual qrc input gives an FF module or,
when the seed lies in O₂(Y), an elementary Y-conjugate span. This discharges
the former extra two-conjugate rank/centralizer premise in source D.1.2.
Source: Aschbacher–Smith, D.1.2(1), 3.1.6 and 3.2.2, pp.172,573–579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

theorem source_reduced_seed_FF_or_elementary_span
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y) :
    let d := source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY
    letI := d.module_elementary
    IsFFModule (ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T d.module_normalized) ∨
      IsElementaryAbelian 2 (ChapterD.conjugateSpan Y V_T) := by
  let d := source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY
  let := d.module_elementary
  by_cases hff : IsFFModule (ChapterD.UniqueFactor.imageRepresentation
      (X ⊔ (T : Subgroup G)) V_T d.module_normalized)
  · exact Or.inl hff
  · exact Or.inr (ChapterD.UniqueFactor.source_elementary_span_of_notFF d hV hff)
end CFSG.Quasithin.Chapter3.Section02

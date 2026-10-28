module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceChiefLayer

/-!
# The genuine qrc chief geometry for the original FSU module

The original local configuration and uniqueness supply D.1.1. In its
inside-core branch, the actual chief series has positive noncentral
count. If that count is one, the newly proved unique-layer theorem
constructs its residual-commutator geometry on these same subgroups.
Both original internal actor alternatives remain in the hypotheses.

Source: Aschbacher–Smith, D.1.4–5 and 3.1.6/3.2.2, pp.175–177,
573–579. The later dual-offender construction remains a source step.
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

theorem source_reduced_seed_chiefLayerGeometry
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T) :
    ChapterD.UniqueFactor.ChiefLayerGeometry Y V_T :=
  ChapterD.UniqueFactor.source_chiefLayerGeometry
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs

theorem source_reduced_seed_noncentralCount_ne_zero
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (s : NoncentralChiefRefinement.SeriesOn ((ChapterD.conjugateSpan Y V_T).subgroupOf Y)) :
    s.noncentralCount ≠ 0 := by
  have hne : V_T ≠ ⊥ := by
    intro he
    exact ReducedNormal.subspaceImage_ne_bot _ _ (hI.ne_bot _)
      (bot_unique ((le_componentOrbit V₀ T).trans_eq he))
  exact ChapterD.UniqueFactor.noncentralCount_ne_zero
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hne hV s

end CFSG.Quasithin.Chapter3.Section02

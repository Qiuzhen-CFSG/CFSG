module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.SourceSolvable

/-!
# The solvable qrc alternatives on both original FSU actor cases

The original reduced seed is nonzero. For every solvable second local group,
apply the complete source qrc alternatives to its actual configuration. The
outside-core, FF, dual-FF, multiple-chief-factor, and full unique-factor
structural branches all retain the original quotient action and subgroups.
Source: Aschbacher–Smith D.1.5 and 3.1.6/3.2.2, pp.177,573–579.
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

theorem source_reduced_seed_solvable_qrc_cases
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable Y) :
    let d := source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY
    letI := d.module_elementary
    let ρ := ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T d.module_normalized
    (¬ V_T ≤ ChapterD.twoCoreIn Y) ∨
    (quadraticRatio ρ ≤ 1 ∧ IsFFModule ρ) ∨
    ChapterD.UniqueFactor.DualFF d ∨
    (quadraticRatio ρ ≤ 2 ∧ IsElementaryAbelian 2 (ChapterD.conjugateSpan Y V_T) ∧
      ∃ s : NoncentralChiefRefinement.SeriesOn ((ChapterD.conjugateSpan Y V_T).subgroupOf Y),
        1 < s.noncentralCount) ∨
    (ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T ∧
      ChapterD.UniqueFactor.StructuralConclusion (X ⊔ (T : Subgroup G)) Y (T : Subgroup G) V_T) := by
  apply ChapterD.UniqueFactor.source_solvable_qrc_cases
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) _ hs
  intro he
  exact ReducedNormal.subspaceImage_ne_bot _ _ (hI.ne_bot _)
    (bot_unique ((le_componentOrbit V₀ T).trans_eq he))

end CFSG.Quasithin.Chapter3.Section02

module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson

/-!
# The complete unique-factor qrc branch on the original FSU module

For either original actor alternative, the genuine qrc configuration in
the inside-core, one-noncentral-chief-factor case satisfies D.1.5(2), (3),
or (5). The FF, dual-FF, and structural alternatives use the original
conjugation image and subgroups. All unique-factor source work is supplied
by the new D.1 proof; the separate multiple-factor and outside-core cases
remain with their source producers.
Source: Aschbacher–Smith, D.1.5 and 3.1.6/3.2.2, pp.177,573–579.
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

theorem source_reduced_seed_uniqueFactor_cases
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T) :
    let d := source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY
    letI := d.module_elementary
    let ρ := ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T d.module_normalized
    (quadraticRatio ρ ≤ 1 ∧ IsFFModule ρ) ∨ ChapterD.UniqueFactor.DualFF d ∨
      ChapterD.UniqueFactor.StructuralConclusion (X ⊔ (T : Subgroup G)) Y (T : Subgroup G) V_T :=
  ChapterD.UniqueFactor.source_uniqueFactor_cases
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs

end CFSG.Quasithin.Chapter3.Section02

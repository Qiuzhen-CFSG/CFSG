module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceDualOffender

/-!
# The original FSU dual-offender alternative

In the inside-core, unique-chief-factor case, the original faithful orbit
module has a dual offender, or the intersection of the two original cores
is normal in the second group and the full orbit is elementary abelian.
Both source FSU actor alternatives are retained. This constructs the
D.1.4 dual branch used in 3.1.6/3.2.2; the remaining residual and Thompson
conclusions are separate source steps.
Source: Aschbacher–Smith, pp.175–176,573–579.
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

theorem source_reduced_seed_dualFF_or_normal_elementary
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T) :
    ChapterD.UniqueFactor.DualFF
        (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) ∨
      (Y ≤ normalizer ((ChapterD.twoCoreIn (X ⊔ (T : Subgroup G)) ⊓
        ChapterD.twoCoreIn Y : Subgroup G) : Set G) ∧
        IsElementaryAbelian 2 (ChapterD.conjugateSpan Y V_T)) :=
  ChapterD.UniqueFactor.source_dualFF_or_normal_elementary
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs

end CFSG.Quasithin.Chapter3.Section02

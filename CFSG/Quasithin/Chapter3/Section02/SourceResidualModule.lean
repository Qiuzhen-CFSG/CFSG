module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceResidualModule

/-!
# The original FSU residual module in the unique-factor branch

Apply the completed D.1.4 residual-module construction to the original
qrc configuration. Either its actual faithful module has a dual offender,
or its residual commutator lies in the second core's center and is a
reduced normal module on the literal second-group carrier.
Both original actor alternatives and quotient conventions are preserved.
Source: Aschbacher–Smith, D.1.4 and 3.1.6/3.2.2, pp.176,573–579.
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

theorem source_reduced_seed_dualFF_or_reduced_residual
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T) :
    ChapterD.UniqueFactor.DualFF
        (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) ∨
      (⁅ChapterD.conjugateSpan Y V_T,(pResidual 2 Y).map Y.subtype⁆ ≤
          (center (ChapterD.twoCoreIn Y)).map (ChapterD.twoCoreIn Y).subtype ∧
        IsPReduced 2
          ((⁅ChapterD.conjugateSpan Y V_T,(pResidual 2 Y).map Y.subtype⁆ : Subgroup G).subgroupOf Y)) :=
  ChapterD.UniqueFactor.source_dualFF_or_reduced_residual
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs

end CFSG.Quasithin.Chapter3.Section02

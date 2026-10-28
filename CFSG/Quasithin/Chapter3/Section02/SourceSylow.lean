module
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceSylow

/-!
# The source D.1.4 Sylow alternative for the original FSU module

The original qrc configuration in the unique-chief-factor, inside-core
case has a dual FF-module or its first two-core is Sylow in its join with
the second group's residual, when that second group is solvable. This
uses the completed D.1.4 Sylow source proof with every residual, action
and embedding unchanged.
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

theorem source_reduced_seed_dualFF_or_residual_sylow
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hV : V_T ≤ ChapterD.twoCoreIn Y)
    (hs : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor Y V_T)
    (hsolv : Group.IsSolvable Y) :
    ChapterD.UniqueFactor.DualFF
        (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) ∨
      Chapter1.IsSylowIn 2 (ChapterD.twoCoreIn (X ⊔ (T : Subgroup G)))
        ((pResidual 2 Y).map Y.subtype ⊔ ChapterD.twoCoreIn (X ⊔ (T : Subgroup G))) :=
  ChapterD.UniqueFactor.source_dualFF_or_sylow
    (source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hY) hV hs hsolv

end CFSG.Quasithin.Chapter3.Section02

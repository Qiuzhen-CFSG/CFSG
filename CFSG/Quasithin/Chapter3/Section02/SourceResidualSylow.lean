module

public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.Chapter3.Section01.ResidualSylow

/-!
# The residual-Sylow obstruction in the original Fundamental Setup

For either original actor alternative, the nonzero reduced seed makes
O₂(XT) nontrivial. Apply the actual 3.1.5 configuration and uniqueness
to source 3.1.1. This excludes O₂(XT) being Sylow in O²(H)O₂(XT) for
every original H in H*(T,M), the contradiction used in the Baumann branch.

The universal source 3.1.1 implication is the precise outstanding input
from the C.5.8 owner. The separate E.2.3 factor argument must produce the
residual-Sylow fact in the noncentral branch of 3.1.7.
Source: Aschbacher–Smith, Lemmas 3.1.7 and 3.2.2(6), pp.575–579.
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

theorem source_reduced_seed_not_residual_sylow
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Chapter1.IsSylowIn 2 ((X ⊔ (T : Subgroup G)).pCoreIn 2)
      ((pResidual 2 Y).map Y.subtype ⊔ (X ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  exact hq.not_residual_sylow h311
    (source_reduced_seed_local_core_ne_bot T X M hXM hTM hG hM hX hc I hI) hu

end CFSG.Quasithin.Chapter3.Section02

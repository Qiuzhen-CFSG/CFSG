module
public import CFSG.Quasithin.Chapter3.Section02.SourceBaumann
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalSource
/-!
# The original FSU Baumann conclusions from C.5.8

Apply the actual common-normal theorem to the original comparison subgroup.
The complete E.2.3 Sylow source then proves both the Thompson commutator
identity and the FF conclusion on the same seed orbit. No independent
3.1.1 premise remains; only the genuine A.3.12 source implication is retained.
Source: Aschbacher–Smith 3.1.7 and 3.2.2(6), printed pp.575–579.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G]
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_M" => componentOrbit V₀ M
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

open Stellmacher

theorem source_reduced_seed_overgroup_conclusions_of_A312
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    :
    letI := source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI
    X = ⁅X, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      IsFFModule (ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T
        (source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI)) :=
  source_reduced_seed_overgroup_conclusions T X M hXM hTM hG hM hX hc I hI
    (Chapter3.source_common_normal_of_A312 hG hA312 T) hu hfix hY
end CFSG.Quasithin.Chapter3.Section02

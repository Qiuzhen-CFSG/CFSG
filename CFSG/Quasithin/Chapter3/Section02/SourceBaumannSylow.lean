module
public import CFSG.Quasithin.Chapter3.Section02.SourceResidualSylow
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow

/-!
# The original FSU application of the linear E.2.3 Sylow conclusion

For both source actor alternatives, uniqueness and the genuine 3.1.1
common-normal implication exclude E.2.3(2)'s actual intrinsic Baumann
Sylow conclusion when J(T) centralizes the original reduced seed orbit.
This is the terminal contradiction in the linear branch of 3.1.7.

The independent producers retain the full E.2.3 classification and
3.1.1/C.5.8 implication. Every subgroup and map here is the original one.
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

theorem source_reduced_seed_not_baumann_residual_sylow
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G))
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Chapter1.IsSylowIn 2 (ChapterB.baumann
        ((T.subtype hY.1.1.2 : Sylow 2 Y) : Subgroup Y))
      (pResidual 2 Y ⊔ ChapterB.baumann
        ((T.subtype hY.1.1.2 : Sylow 2 Y) : Subgroup Y)) := by
  intro hs
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  exact source_reduced_seed_not_residual_sylow T X M hXM hTM hG hM hX hc I hI h311 hu hY
    (hq.residual_sylow_of_baumann_sylow hJ hs)

end CFSG.Quasithin.Chapter3.Section02

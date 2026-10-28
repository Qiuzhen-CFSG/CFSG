module
public import CFSG.Quasithin.Chapter3.Section02.SourceThompson
public import CFSG.Quasithin.Chapter3.Section02.SourceResidualSylow
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSylow

/-!
# FSU clause six for every original comparison subgroup

The reduced seed and its original Sylow orbit give the genuine qrc
configuration. The complete E.2.3 residual-Sylow theorem applies to every
comparison subgroup in the full known-simple campaign, so a centralized Thompson action contradicts the
common-normal conclusion and uniqueness. Nonzero fixed vectors exclude
the central omega-center case. This proves the original commutator and
FF-module conclusions without a solvability or model-family premise.

The remaining earlier input is exactly 3.1.1/C.5.8, with its existing
source owner. Source: Aschbacher–Smith 3.1.7 and 3.2.2(6), pp.575–579.
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

/-- For every original comparison subgroup, the Thompson subgroup moves
V; the genuine C.5.8/3.1.1 implication remains explicit. -/
theorem source_reduced_seed_thompson_moves_of_overgroup
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G) := by
  intro hJ
  have hz := source_reduced_seed_omega_center_not_central
    T X M hXM hTM hG hM hX hc I hI hfix hu hY
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  have hs := hq.residual_sylow_source hG hM hu hJ hz
  exact source_reduced_seed_not_residual_sylow T X M hXM hTM hG hM hX hc I hI h311 hu hY hs

/-- Both original conclusions of 3.2.2(6) on every comparison branch. -/
theorem source_reduced_seed_overgroup_conclusions
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    :
    letI := source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI
    X = ⁅X, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      IsFFModule (ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T
        (source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI)) := by
  have hj := source_reduced_seed_thompson_moves_of_overgroup
    T X M hXM hTM hG hM hX hc I hI h311 hu hfix hY
  exact ⟨source_reduced_seed_thompson_commutator T X M hXM hTM hG hM hX hc I hI hj,
    source_reduced_seed_module_isFF T X M hXM hTM hG hM hX hc I hI hj⟩
end CFSG.Quasithin.Chapter3.Section02

module
public import CFSG.Quasithin.Chapter3.Section02.SourceThompson
public import CFSG.Quasithin.Chapter3.Section02.SourceResidualSylow
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSolvableBaumann

/-!
# The full solvable comparison branch of FSU clause six

The original reduced orbit supplies the genuine qrc configuration. If a
solvable member of H*(T,M) is present, the complete solvable E.2.3 theorem
forces the residual Sylow conclusion whenever J(T) centralizes V. The
original common-normal theorem and uniqueness exclude that conclusion.
Nonzero fixed vectors exclude the alternative central omega-center case.
Thus J(T) moves V, giving both X=[X,J(T)] and the actual FF-module.

The only earlier-source implication retained is 3.1.1/C.5.8, with its
existing producer. No module chart, classification certificate or Sylow
condition remains in this solvable branch.
Source: Aschbacher–Smith 3.1.7 and 3.2.2(6), printed pp.575–579.
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
local notation "V_M" => componentOrbit V₀ M
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

open Stellmacher

/-- In the actual solvable comparison branch, the Thompson subgroup moves
V; the genuine C.5.8/3.1.1 implication remains explicit. -/
theorem source_reduced_seed_thompson_moves_of_solvable_overgroup
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsolv : Group.IsSolvable Y) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G) := by
  intro hJ
  have hz := source_reduced_seed_omega_center_not_central
    T X M hXM hTM hG hM hX hc I hI hfix hu hY
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  have hs := hq.residual_sylow_of_solvable hG hM hu hJ hz hsolv
  exact source_reduced_seed_not_residual_sylow T X M hXM hTM hG hM hX hc I hI h311 hu hY hs

/-- Both original conclusions of 3.2.2(6) on the solvable comparison branch. -/
theorem source_reduced_seed_solvable_overgroup_conclusions
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → Chapter3.HasCommonNormal A H R)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsolv : Group.IsSolvable Y) :
    letI := source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI
    X = ⁅X, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      IsFFModule (ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T
        (source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI)) := by
  have hj := source_reduced_seed_thompson_moves_of_solvable_overgroup
    T X M hXM hTM hG hM hX hc I hI h311 hu hfix hY hsolv
  exact ⟨source_reduced_seed_thompson_commutator T X M hXM hTM hG hM hX hc I hI hj,
    source_reduced_seed_module_isFF T X M hXM hTM hG hM hX hc I hI hj⟩
end CFSG.Quasithin.Chapter3.Section02

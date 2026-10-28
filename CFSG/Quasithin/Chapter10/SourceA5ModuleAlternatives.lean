module
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage
public import CFSG.Quasithin.Chapter10.SourceA5ProperSeedPointControl
public import CFSG.Quasithin.Chapter10.SourceA5BaumannNormalizerControl

/-!
# The original minimal A₅ module: tensor or separated moved action

The same-seed and proper-seed source proofs now cover the original seed
dichotomy. Both give equality of the full and local modules. The first
constructs the marked tensor model; the second gives moved-quotient
irreducibility, crossed centralization and moved-normalizer containment.
The actual multiple-overgroup premise supplies the full cubic bound.

The point-control consumer removes the proper-seed assumption when the
independent tensor exclusion is available. The completed source 10.2.1 supplies
Baumann containment. Only the local cubic bound and marked point-component
inspection remain as separate earlier source obligations in this consumer.

Source: Aschbacher--Smith D.3.5--9, 9.3--4 and 10.2.9--12,
printed pp.195--201, 733--737 and 750--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance moduleAlternativesMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- Both original seed branches give full/local equality and the complete
marked alternative needed by the tensor and weak-closure source arguments. -/
theorem source_a5_original_tensor_or_moved_control
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hlocal : SourceLocalModuleCubicBound D)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.fullModule = D.moduleSubgroup ∧
      (Nonempty (SourceA5TensorModel D e) ∨
        (originalMovedQuotientAction D e).IsIrreducible ∧
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) := by
  by_cases hseed : D.seed = D.moduleSubgroup
  · have hbound := source_full_module_cubic_bound_of_many D hmany
    exact ⟨(source_a5_local_eq_full_of_seed_eq_local D e hn hD hseed hbound).symm,
      Or.inl (source_a5_original_tensor_model_of_seed_eq_local D e hn hD hseed hbound)⟩
  · obtain ⟨hfull,hi,hcross,hnorm⟩ :=
      source_a5_original_proper_seed_control D e hn ht htn hD hseed hlocal hmany
    exact ⟨hfull,Or.inr ⟨hi,hcross,hnorm⟩⟩

/-- The independent tensor exclusion supplies the proper-seed premise of
the original point and weak-closure argument. -/
theorem source_a5_seed_ne_local_of_no_tensor
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e)) :
    D.seed ≠ D.moduleSubgroup := by
  intro hseed
  exact hnot (source_a5_original_tensor_model_of_seed_eq_local D e hn hD hseed
    (source_full_module_cubic_bound_of_many D hmany))

/-- Actual point control and the weak-closure lower bound after the original
tensor branch has been excluded; no seed dichotomy remains in the inputs. -/
theorem source_a5_point_control_of_no_tensor
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hlocal : SourceLocalModuleCubicBound D)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  have hproper := source_a5_seed_ne_local_of_no_tensor D e hn hD hmany hnot
  have h1021 := source_a5_baumann_normalizer_le D e hn
  exact ⟨source_a5_proper_seed_point_centralizers D e hn ht htn hD hproper hlocal
      hmany h1021 hinspect,
    source_a5_proper_seed_globalW_gt_one D e hn ht htn hD hproper hlocal
      hmany h1021 hinspect⟩

end CFSG.Quasithin.Chapter10

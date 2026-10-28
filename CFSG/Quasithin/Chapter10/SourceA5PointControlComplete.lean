module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleAlternativesComplete
public import CFSG.Quasithin.Chapter10.SourceA5PointInspectionComplete

/-!
# Original A₅ point control after tensor exclusion

The completed local cubic source theorem removes the last numerical premise
of the point-control argument. The original minimal setup now has point
centralizer containment and the weak-closure lower bound once its tensor
model is excluded. The original multiple-overgroup hypothesis remains the
source of the outside-maximal guard.

Source: Aschbacher--Smith 3.1.8 and 10.2.9--12, printed pp.576,750--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

/-- Tensor exclusion is the only independent source input left in the
chosen original module's point-control and weak-closure argument. -/
theorem source_a5_point_control_after_tensor_exclusion_of_many
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e)) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) :=
  source_a5_point_control_after_tensor_exclusion D e hn ht htn hD
    (source_local_module_cubic_bound_of_many D hmany) hmany hnot

end CFSG.Quasithin.Chapter10

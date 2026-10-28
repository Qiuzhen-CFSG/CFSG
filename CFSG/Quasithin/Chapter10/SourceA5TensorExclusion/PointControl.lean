module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoAssembly
public import CFSG.Quasithin.Chapter10.SourceA5PointControlComplete

/-!
# Point control from the conditional tensor assembly

Apply the generation-two contradiction to the original point-control
consumer. The earlier Cartan/amalgam and later model inputs remain
explicit until their independent source proofs are supplied.
Source: Aschbacher--Smith 9.3 and10.2.9--12, pp.732--735,750--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Actual original point control, consuming the assembled tensor exclusion. -/
theorem source_a5_point_control_of_tensor_source_inputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnormal : ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion)
    (hplane : ∀ m : SourceA5TensorModel D e, m.SymplecticPlaneRecognition) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) :=
  source_a5_point_control_after_tensor_exclusion_of_many D e hn ht htn hD hmany
    (source_a5_tensor_exclusion_of_source_inputs D e (source_maximalOutside_of_many D hmany)
      hnormal hzero hcontain hrows hplane)

end CFSG.Quasithin.Chapter10


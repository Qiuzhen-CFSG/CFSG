module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Setup
public import CFSG.Quasithin.ClassificationModels
import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceMarkedTriality

/-! The original eight-field ambient recognition behind a narrow public boundary. -/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRecognitionInterface
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
/-- Original large-parabolic recognition, with no supplied comparison,
marking, completion, or apartment-exchange premise. -/
theorem source_eight_theoremE : ClassificationModels.IsTheoremEModel G :=
  SourceMarkedTriality.source_eight_theoremE hG T hempty hM hu hmany hcard e H hH eR

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRecognitionInterface

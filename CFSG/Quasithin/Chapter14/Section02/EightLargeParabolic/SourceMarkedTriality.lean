module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceApartmentExchange
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNativeComparison
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Recognition

/-!
# Original mixed-field recognition from the actual apartment

The original source supplies its compatible Cartan and faithful six-path
exchange. Native comparison therefore marks the literal two parabolics and
their full overlap. Ambient recognition on these same markings identifies G
with the binary triality model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceMarkedTriality
open ChapterF.Source ChapterF.Source.SuzukiContainment
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
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)

set_option maxHeartbeats 800000 in
/-- The actual original L₂(8) source has its marked triality realization,
with both literal endpoints and their entire intersection retained. -/
theorem source_marked_triality : Nonempty (MarkedTriality T M Mc H) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let c := ReducedCartan.chosenCartans h
  obtain ⟨d,hexchange⟩ := SourceApartmentExchange.source_apartment_exchange
    hG T hempty hM hu hmany hcard e H hH eR c
  exact SourceNativeComparison.source_marked_triality_of_six_exchange
    hG T hempty hM hu hmany hcard e H hH eR c d.reflection
    d.fixes d.moves d.squares d.normalizes hexchange

/-- Original large-parabolic recognition, with no supplied comparison,
marking, completion, or apartment-exchange premise. -/
theorem source_eight_theoremE : ClassificationModels.IsTheoremEModel G := by
  obtain ⟨r⟩ := source_marked_triality hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨f,_,_⟩ := source_marked_ambient_recognition hG hempty hM hu hmany hcard e hH r
  exact ClassificationModels.IsTheoremEModel.triality
    ((_root_.Triality.Standard.isTrialityGroupAt_two_iff G).mpr ⟨f⟩)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceMarkedTriality

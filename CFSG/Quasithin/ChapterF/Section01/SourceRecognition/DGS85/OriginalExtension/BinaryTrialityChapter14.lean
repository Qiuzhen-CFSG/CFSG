module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryTrialityRestoration
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeometry

/-!
# Binary triality restoration on the original Chapter 14 pair

Restore the genuine F.1.1 pair selected by the prescribed residual quotient
eR. The inclusion diagram has the original H, full second parabolic
Y T (M ∩ O²(H)), and their entire intersection as its three groups. The
constructed maps use the existing source equalities and the restored reduced
marking, retaining both commuting squares and the odd Borel factor.

The actual downstream consumers then give the original Sylow and core orders,
the ambient triality order, and the literal endpoint equalities. Reduced
marked recognition remains explicit; no ambient group isomorphism is inferred.

Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith 14.2.16–19,
pp.986–987, and F.1.9–12, pp.261–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source.DGS85.OriginalExtension
open _root_.Triality.Standard
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
  (r : Iso (reducedAmalgam (locals T M Mc H) (T : Subgroup G))
    (TrialityNative.amalgam 1 Nat.zero_lt_one false))

/-- Restore the original H, full second parabolic and whole intersection
from the reduced marking on the literal source pair selected by eR. -/
def markedTrialityOfReduced : MarkedTriality T M Mc H := by
  let hf := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  obtain ⟨h0,h1,hB,hI,_⟩ := source_parabolics hG T hempty hM hu hmany hcard e H hH eR
  let J : Iso (amalgam T M Mc H)
      (originalAmalgam (locals T M Mc H) (T : Subgroup G)) := {
    left := MulEquiv.subgroupCongr h0.symm
    right := MulEquiv.subgroupCongr h1.symm
    middle := MulEquiv.subgroupCongr (hB.trans hI.symm).symm
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  exact J.trans (BinaryTriality.originalIso hf false r)

include hG hempty hM hu hmany hcard e hH eR r in
/-- The restored comparison supplies the actual original Sylow and core
orders used downstream, without a separate original marking premise. -/
theorem source_original_orders_of_reduced_triality :
    Nat.card T = 4096 ∧ Nat.card (H.pCoreIn 2) = 512 ∧
      Nat.card ((secondParabolic T M Mc H).pCoreIn 2) = 2048 := by
  let f := markedTrialityOfReduced hG T hempty hM hu hmany hcard e H hH eR r
  exact ⟨source_sylow_card f hH.1.1.2,firstCore_card f,secondCore_card f⟩

include hG hempty hM hu hmany hcard e hH eR r in
/-- The existing full-geometry consumer now needs only reduced recognition;
its ambient order and literal endpoint equalities have no original-model premise. -/
theorem source_full_geometry_of_reduced_triality :
    Nat.card G = Nat.card (BinaryCarrier 1 Nat.zero_lt_one) ∧
      Mc = H ∧ secondParabolic T M Mc H = M := by
  let f := markedTrialityOfReduced hG T hempty hM hu hmany hcard e H hH eR r
  exact ⟨source_card_eq_triality hG hempty hM hu hmany hcard e hH f,
    source_endpoints_eq hG hempty hM hu hmany hcard e hH f⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

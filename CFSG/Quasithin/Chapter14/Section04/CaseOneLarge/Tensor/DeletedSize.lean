module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedAmalgam
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Order
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.Basic
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.Local

/-!
# The mixed F.1.12 consumer in the deleted tensor branch

The literal H∞, I₂ and T satisfy all hypotheses of the existing mixed
A₅/S₃ size contract: the preceding amalgam supplies F.1.1, the ambient
counterexample supplies quasithinness, and T remains Sylow in G₀T.
The cubic quotient makes its Borel normalize T. The numerical conclusion
|T| ≤ 256 contradicts the order-512 tensor closure contained in T.

This is conditional assembly. The numerical source theorem is owned by
`qt-d-tensor-mixed-size-bound`; it is not proved here. The shared contract
is used directly, so no stronger structural recognition premise is added.
The earlier faithful-classification and setup inputs retain their original
owners. The conjugator and all quotient markings remain unchanged.

Source: Aschbacher--Smith, 14.4.10(3), printed p.1011, and F.1.12(I),
printed pp.262--264. The order argument replaces only the final inspection
of the extraspecial first parabolic.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Every literal premise of the mixed F.1.12 size theorem is constructed. -/
theorem source_tensor_deleted_mixed_hypotheses (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ChapterF.Source.HypothesisF11 ![component F.H, F.I₂ L] (T : Subgroup G) ∧
      IsQuasithin (ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G)) ∧
      Chapter1.IsSylowIn 2 (T : Subgroup G)
        (ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G)) ∧
      Nonempty (coreQuotient (component F.H) ≃* AltFive) ∧
      Nonempty (coreQuotient (F.I₂ L) ≃* Three) ∧
      ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) ≤ normalizer (T : Set G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  obtain ⟨e, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare
      (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  have hF := source_tensor_deleted_amalgam d earlier hq chosen structural alternatives
    classification F hne hZ g hg hgP hgH c hdel
  have hT : (T : Subgroup G) ≤
      ChapterF.Source.generated ![component F.H, F.I₂ L] (T : Subgroup G) := le_sup_right
  exact ⟨hF, d.qtke.quasithin.subgroup _,
    ⟨T.subtype hT, map_subgroupOf_eq_of_le hT⟩,
    ⟨TensorDeleted.componentQuotient (starComponentEquiv hAD c.actor)⟩,
    ⟨e⟩, hF.cubic_borel_normalizes_S 1 e⟩

/-- The mixed size theorem excludes the actual deleted tensor row. Its independent
source proof remains an explicit input. -/
theorem source_tensor_deleted_contradiction_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) : False := by
  obtain ⟨hF, hqt, hT, hK, hI, hB⟩ := source_tensor_deleted_mixed_hypotheses
    d earlier hq chosen structural alternatives classification F hne hZ g hg hgP hgH c hdel
  have hl := source_tensor_sylow_card_lower_bound d earlier hq chosen structural alternatives
    F hne hZ c
  have hu := size (component F.H) (F.I₂ L) (T : Subgroup G) hF hqt hT hK hI hB
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

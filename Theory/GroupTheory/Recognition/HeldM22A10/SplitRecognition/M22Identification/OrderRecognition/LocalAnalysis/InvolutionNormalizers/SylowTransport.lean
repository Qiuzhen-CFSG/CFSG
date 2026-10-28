module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ModelSylow
/-!
# Transport of the Case II Sylow complements

The image of the coordinate subgroup has order 128, equal to the order of
an ambient Sylow two-subgroup. It is therefore an ambient Sylow subgroup
for every coordinate equivalence k. Both E and F lie in it, have complements
in it, and are normalized by it. This supplies the local splitting input
for Gaschütz's theorem without identifying this Sylow subgroup with the
originally chosen `D.sylow`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, p.4.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem modelT_map_card : Nat.card (modelT.map (into D k)) = 128 := by
  rw [← Nat.card_congr (modelT.equivMapOfInjective (into D k) (into_injective D k)).toEquiv]
  exact modelT_card

/-- The ambient Sylow subgroup supplied by the arbitrary coordinate map. -/
@[expose] public def caseIISylow : Sylow 2 G := Sylow.ofCard (modelT.map (into D k)) (by
  rw [modelT_map_card]
  exact (D.sylow_card).symm.trans D.sylow.card_eq_multiplicity)

public theorem E_le_caseIISylow : E D k ≤ caseIISylow D k := by
  change E D k ≤ modelT.map (into D k)
  rw [← modelE_map D k]
  exact map_mono modelE_le_modelT

public theorem F_le_caseIISylow : F D k ≤ caseIISylow D k := by
  change F D k ≤ modelT.map (into D k)
  rw [← modelF_map D k]
  exact map_mono modelF_le_modelT

public theorem caseIISylow_le_normalizer_E :
    (caseIISylow D k : Subgroup G) ≤ normalizer (E D k : Set G) := by
  change modelT.map (into D k) ≤ normalizer (E D k : Set G)
  rw [← modelE_map D k]
  let : modelE.Normal := by unfold modelE; infer_instance
  exact (map_mono (show modelT ≤ normalizer (modelE : Set TwistedModel) from
    normalizer_eq_top (H := modelE) ▸ le_top)).trans (le_normalizer_map _)

public theorem caseIISylow_le_normalizer_F :
    (caseIISylow D k : Subgroup G) ≤ normalizer (F D k : Set G) := by
  change modelT.map (into D k) ≤ normalizer (F D k : Set G)
  rw [← modelF_map D k, ← modelF_normalizer]
  exact le_normalizer_map _

private theorem complement_in_image (P R : Subgroup TwistedModel)
    (hP : P ≤ modelT) (hR : R ≤ modelT)
    (hc : Nat.card P * Nat.card R = 128) (hd : P ⊓ R = ⊥) :
    ((P.map (into D k)).subgroupOf (caseIISylow D k)).IsComplement'
      ((R.map (into D k)).subgroupOf (caseIISylow D k)) := by
  have hPle : P.map (into D k) ≤ caseIISylow D k := map_mono hP
  have hRle : R.map (into D k) ≤ caseIISylow D k := map_mono hR
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_congr (subgroupOfEquivOfLe hPle).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hRle).toEquiv,
      ← Nat.card_congr (P.equivMapOfInjective (into D k) (into_injective D k)).toEquiv,
      ← Nat.card_congr (R.equivMapOfInjective (into D k) (into_injective D k)).toEquiv,
      hc]
    exact (modelT_map_card D k).symm
  · rw [disjoint_iff]
    ext x
    change (x : G) ∈ P.map (into D k) ⊓ R.map (into D k) ↔ x = 1
    rw [← map_inf _ _ _ (into_injective D k), hd, Subgroup.map_bot, mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

public theorem E_sylow_complement : ∃ K : Subgroup (caseIISylow D k),
    ((E D k).subgroupOf (caseIISylow D k)).IsComplement' K := by
  refine ⟨(modelEComplement.map (into D k)).subgroupOf (caseIISylow D k), ?_⟩
  rw [← modelE_map D k]
  exact complement_in_image D k modelE modelEComplement modelE_le_modelT
    modelEComplement_le_modelT (by rw [modelE_card, modelEComplement_card]) modelEComplement_inf

public theorem F_sylow_complement : ∃ K : Subgroup (caseIISylow D k),
    ((F D k).subgroupOf (caseIISylow D k)).IsComplement' K := by
  refine ⟨(modelFComplement.map (into D k)).subgroupOf (caseIISylow D k), ?_⟩
  rw [← modelF_map D k]
  exact complement_in_image D k modelF modelFComplement modelF_le_modelT
    modelFComplement_le_modelT (by rw [modelF_card, modelFComplement_card]) modelFComplement_inf

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII

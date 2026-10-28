module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.NonsplitStructure.Quotient

/-!
# Actual first-parabolic conjugation on the wreath quotient

Conjugation in the degree-24 carrier restricts to outerCore when that subgroup
is normalized by the first parabolic. It fixes the original z and descends to
the actual quotient, then transports through outerQuotientEquiv. Evaluation
formulas retain both original quaternion embeddings and the nonsplit lift;
the lift interchanges the marked factors. Quaternion-core normalization gives
invariance of the wreath base.

The two normalization premises are explicit and belong to the LocalCore/final
first-parabolic assembly. Neither premise is used for the quotient or structural
calculations. This is the actual conjugation action, not the split model's action.

Source: Aschbacher--Smith, 14.2.21, printed p.988, refs/quasithin.pdf.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open QuaternionSwapModel (W quaternionQuotient)

/-- Literal first-parabolic conjugation on the concrete core; normality is explicit. -/
def outerConjugation
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier)) :
    firstParabolic →* MulAut outerCore :=
  outerCore.normalizerMonoidHom.comp (Subgroup.inclusion hn)

theorem outerConjugation_apply
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (x : outerCore) :
    (outerConjugation hn h x).val = h.val * x.val * h.val⁻¹ := rfl

theorem outerConjugation_marked
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) : outerConjugation hn h outerMarked = outerMarked := by
  apply Subtype.ext
  change h.val * z * h.val⁻¹ = z
  have hc := Subgroup.mem_centralizer_singleton_iff.mp h.property
  rw [hc, mul_inv_cancel_right]

/-- The action on the quotient is induced by actual conjugation, not an unrelated model action. -/
noncomputable def outerQuotientAction (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier)) :
    firstParabolic →* MulAut OuterQuotient := by
  letI : (distinguished.subgroupOf outerCore).Characteristic := by
    rw [← center_outerCore_eq m]
    infer_instance
  exact (Subgroup.quotientAut (distinguished.subgroupOf outerCore)).comp (outerConjugation hn)

theorem outerQuotientAction_mk (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (x : outerCore) :
    outerQuotientAction m hn h (outerProjection x) =
      outerProjection (outerConjugation hn h x) := by
  let : (distinguished.subgroupOf outerCore).Characteristic := by
    rw [← center_outerCore_eq m]
    infer_instance
  unfold outerQuotientAction
  exact Subgroup.quotientAut_apply_mk _ _ x

/-- The retained first-parabolic action in the marked E4 wreath coordinates. -/
noncomputable def outerWreathAction (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier)) :
    firstParabolic →* MulAut W :=
  (MulAut.congr (outerQuotientEquiv m)).toMonoidHom.comp (outerQuotientAction m hn)

theorem outerWreathAction_equiv (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (x : OuterQuotient) :
    outerWreathAction m hn h (outerQuotientEquiv m x) =
      outerQuotientEquiv m (outerQuotientAction m hn h x) := by
  change outerQuotientEquiv m (outerQuotientAction m hn h
    ((outerQuotientEquiv m).symm (outerQuotientEquiv m x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Evaluation on every representative is the original ambient conjugation. -/
theorem outerWreathAction_evaluation (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (x : outerCore) :
    outerWreathAction m hn h (outerWreathMap m x) =
      outerWreathMap m ⟨h.val * x.val * h.val⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hn h.property) x.val).mp x.property⟩ := by
  change outerWreathAction m hn h (outerQuotientEquiv m (outerProjection x)) = _
  rw [outerWreathAction_equiv, outerQuotientAction_mk]
  rfl

theorem outerWreathAction_left (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (q : QuaternionGroup 2) :
    outerWreathAction m hn h
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q)) =
        outerWreathMap m (outerConjugation hn h (outerLeft q)) := by
  rw [← outerWreathMap_left m q]
  exact outerWreathAction_evaluation m hn h (outerLeft q)

theorem outerWreathAction_right (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) (q : QuaternionGroup 2) :
    outerWreathAction m hn h
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q)) =
        outerWreathMap m (outerConjugation hn h (outerRight q)) := by
  rw [← outerWreathMap_right m q]
  exact outerWreathAction_evaluation m hn h (outerRight q)

theorem outerWreathAction_swap (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (h : firstParabolic) :
    outerWreathAction m hn h
      (QuaternionSwapModel.rawWreathMap QuaternionSwapModel.swapRaw) =
        outerWreathMap m (outerConjugation hn h outerSwap) := by
  rw [← outerWreathMap_swap m]
  exact outerWreathAction_evaluation m hn h outerSwap

theorem outerWreathAction_mem_base (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (hk : firstParabolic ≤ Subgroup.normalizer (quaternionCore : Set Carrier))
    (h : firstParabolic) (w : W) (hw : w ∈ QuaternionSwapModel.base) :
    outerWreathAction m hn h w ∈ QuaternionSwapModel.base := by
  obtain ⟨x,rfl⟩ := outerWreathMap_surjective m w
  rw [outerWreathAction_evaluation, outerWreathMap_mem_base]
  exact (Subgroup.mem_normalizer_iff.mp (hk h.property) x.val).mp
    ((outerWreathMap_mem_base m x).mp hw)

theorem outerWreathAction_base (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (hk : firstParabolic ≤ Subgroup.normalizer (quaternionCore : Set Carrier))
    (h : firstParabolic) :
    QuaternionSwapModel.base.map (outerWreathAction m hn h).toMonoidHom =
      QuaternionSwapModel.base := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact outerWreathAction_mem_base m hn hk h w hw
  · intro w hw
    refine ⟨outerWreathAction m hn h⁻¹ w,
      outerWreathAction_mem_base m hn hk h⁻¹ w hw, ?_⟩
    simp

/-- For actors in the concrete core the action is inner conjugation in W. -/
theorem outerWreathAction_core (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (g : outerCore) (w : W) :
    outerWreathAction m hn ⟨g.val,outerCore_centralizes_z g.property⟩ w =
      outerWreathMap m g * w * (outerWreathMap m g)⁻¹ := by
  obtain ⟨x,rfl⟩ := outerWreathMap_surjective m w
  rw [outerWreathAction_evaluation, ← map_inv, ← map_mul, ← map_mul]
  rfl

def swapActor : firstParabolic := ⟨nonsplitSwap,nonsplitSwap_mem_firstParabolic⟩

/-- The nonsplit lift interchanges the original marked quaternion factors. -/
theorem outerWreathAction_swap_left (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (q : QuaternionGroup 2) :
    outerWreathAction m hn swapActor
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q)) =
        QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q) := by
  rw [outerWreathAction_left]
  have he : outerConjugation hn swapActor (outerLeft q) = outerRight q :=
    Subtype.ext (nonsplitSwap_left q)
  rw [he, outerWreathMap_right]

theorem outerWreathAction_swap_right (m : InnerModel)
    (hn : firstParabolic ≤ Subgroup.normalizer (outerCore : Set Carrier))
    (q : QuaternionGroup 2) :
    outerWreathAction m hn swapActor
      (QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q)) =
        QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q) := by
  rw [outerWreathAction_right]
  have he : outerConjugation hn swapActor (outerRight q) = outerLeft q :=
    Subtype.ext (nonsplitSwap_right q)
  rw [he, outerWreathMap_left]

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

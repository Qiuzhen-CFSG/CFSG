module
public import Theory.GroupTheory.QuaternionSwapModel
public import Theory.Mathieu.M12.SmallParabolicPair.Core
public import Theory.GroupTheory.CentralProductEquivalence

/-!
# Comparing the swap model's quaternion core with the concrete M₁₂ core

The two quaternion embeddings in `QuaternionSwapModel.QK` and the concrete
Witt-design `M12SmallPair.core` have exactly the same overlap. Gluing the
prescribed factor maps yields an actual multiplicative equivalence. Its two
restriction formulas preserve all marked quaternion generators, and in
particular its central involution maps to the original `M12SmallPair.z`.

The overlap is checked on the two eight-element domains; the existing
central-product equivalence theorem supplies the global map. This comparison
concerns the order-32 cores only. It does not identify the order-64 swap model
with an Aut(M₁₂) two-core or construct the outer parabolic pair.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005),
`refs/quasithin.pdf`.
-/

namespace Sporadic.Mathieu.M12SmallPair.SwapCoreCoordinates
open Subgroup
private noncomputable abbrev D := QuaternionSwapModel.coreQuaternionData
private noncomputable abbrev E := M12SmallPair.coreQuaternionData

private noncomputable def coordinateLeft : QuaternionGroup 2 ≃* D.left :=
  (MonoidHom.ofInjective QuaternionSwapModel.leftEmbedding_injective).trans
    (subgroupOfEquivOfLe
      (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left)).symm
private noncomputable def coordinateRight : QuaternionGroup 2 ≃* D.right :=
  (MonoidHom.ofInjective QuaternionSwapModel.rightEmbedding_injective).trans
    (subgroupOfEquivOfLe
      (show QuaternionSwapModel.rightFactor ≤ QuaternionSwapModel.QK from le_sup_right)).symm
private noncomputable def concreteLeft : QuaternionGroup 2 ≃* E.left :=
  (MonoidHom.ofInjective M12SmallPair.leftEmbedding_injective).trans
    (subgroupOfEquivOfLe (show M12SmallPair.leftFactor ≤ core from le_sup_left)).symm
private noncomputable def concreteRight : QuaternionGroup 2 ≃* E.right :=
  (MonoidHom.ofInjective M12SmallPair.rightEmbedding_injective).trans
    (subgroupOfEquivOfLe (show M12SmallPair.rightFactor ≤ core from le_sup_right)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem overlap (q r : QuaternionGroup 2) :
    QuaternionSwapModel.leftEmbedding q = QuaternionSwapModel.rightEmbedding r ↔
      M12SmallPair.leftEmbedding q = M12SmallPair.rightEmbedding r := by
  change QuaternionSwapModel.projection (QuaternionSwapModel.leftRaw q) =
    QuaternionSwapModel.projection (QuaternionSwapModel.rightRaw r) ↔ _
  rw [QuaternionSwapModel.projection_eq_iff]
  have h : ∀ q r : QuaternionGroup 2,
      ((QuaternionSwapModel.leftRaw q)⁻¹ * QuaternionSwapModel.rightRaw r = 1 ∨
        (QuaternionSwapModel.leftRaw q)⁻¹ * QuaternionSwapModel.rightRaw r = QuaternionSwapModel.killed) ↔
      M12SmallPair.leftEmbedding q = M12SmallPair.rightEmbedding r := by
    decide +kernel
  exact h q r

private theorem exists_comparison : ∃ e : QuaternionSwapModel.QK ≃* core,
    (∀ q, e (coordinateLeft q) = (concreteLeft q : core)) ∧
    (∀ q, e (coordinateRight q) = (concreteRight q : core)) := by
  obtain ⟨e,hl,hr⟩ := exists_mulEquiv_of_central_products
    D.left D.right E.left E.right
    (fun b c => D.commute b b.property c c.property)
    (fun b c => E.commute b b.property c c.property) D.span E.span
    (coordinateLeft.symm.trans concreteLeft) (coordinateRight.symm.trans concreteRight) (by
      intro b c
      obtain ⟨q,rfl⟩ := coordinateLeft.surjective b
      obtain ⟨r,rfl⟩ := coordinateRight.surjective c
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [Subtype.ext_iff, Subtype.ext_iff]
      exact overlap q r)
  refine ⟨e,fun q => ?_,fun q => ?_⟩
  · simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hl (coordinateLeft q)
  · simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hr (coordinateRight q)

/-- The core isomorphism extending both fixed quaternion embeddings. -/
public noncomputable def coreEquiv : QuaternionSwapModel.QK ≃* core := exists_comparison.choose

public theorem coreEquiv_left (q : QuaternionGroup 2) :
    (coreEquiv ⟨QuaternionSwapModel.leftEmbedding q,
      (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left) ⟨q,rfl⟩⟩ : M12) =
      M12SmallPair.leftEmbedding q :=
  congrArg (fun x : core => (x : M12)) (exists_comparison.choose_spec.1 q)

public theorem coreEquiv_right (q : QuaternionGroup 2) :
    (coreEquiv ⟨QuaternionSwapModel.rightEmbedding q,
      (show QuaternionSwapModel.rightFactor ≤ QuaternionSwapModel.QK from le_sup_right) ⟨q,rfl⟩⟩ : M12) =
      M12SmallPair.rightEmbedding q :=
  congrArg (fun x : core => (x : M12)) (exists_comparison.choose_spec.2 q)

public theorem coreEquiv_marked :
    (coreEquiv ⟨QuaternionSwapModel.z, QuaternionSwapModel.Z_le_QK
      ((QuaternionSwapModel.mem_Z _).mpr (Or.inr rfl))⟩ : M12) = M12SmallPair.z := by
  rw [show (⟨QuaternionSwapModel.z, _⟩ : QuaternionSwapModel.QK) =
      ⟨QuaternionSwapModel.leftEmbedding (QuaternionGroup.a 2),
        (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left)
          ⟨QuaternionGroup.a 2,rfl⟩⟩ from rfl,
    coreEquiv_left]
  decide +kernel

end Sporadic.Mathieu.M12SmallPair.SwapCoreCoordinates

module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Normalizers

/-!
# The first M₁₂ parabolic's two-core and its residual action

The concrete quaternion central product is the two-core of the centralizer of
`z`, of order 192 with quotient S₃. Conjugation by the full first parabolic
preserves both marked factors, hence its two-residual does too. The action
homomorphisms below retain the ambient conjugation formula and agree exactly
with the previously specified cubic witness.

Source: the M₁₂ local model used in Aschbacher–Smith, Hypothesis 14.2.1 and
Lemma 14.2.21. This proves the concrete local input, not the full classification
assertion of that lemma.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair

theorem firstParabolic_normalizes_core :
    firstParabolic ≤ Subgroup.normalizer (core : Set M12) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer core_le_firstParabolic).mp inferInstance

/-- Conjugation in M₁₂, restricted to the actual two-core. -/
def firstParabolicCoreAction : firstParabolic →* MulAut core :=
  core.normalizerMonoidHom.comp (Subgroup.inclusion firstParabolic_normalizes_core)

def residualCoreAction : pResidual 2 firstParabolic →* MulAut core :=
  firstParabolicCoreAction.comp (pResidual 2 firstParabolic).subtype

theorem residualCoreAction_apply (g : pResidual 2 firstParabolic) (q : core) :
    (residualCoreAction g q : M12) = (g.val : M12) * q * (g.val : M12)⁻¹ := rfl

theorem residual_normalizes_left :
    (pResidual 2 firstParabolic).map firstParabolic.subtype ≤
      Subgroup.normalizer (leftFactor : Set M12) := by
  rintro _ ⟨g,_,rfl⟩
  exact firstParabolic_normalizes_left g.property

theorem residual_normalizes_right :
    (pResidual 2 firstParabolic).map firstParabolic.subtype ≤
      Subgroup.normalizer (rightFactor : Set M12) := by
  rintro _ ⟨g,_,rfl⟩
  exact firstParabolic_normalizes_right g.property

theorem residualCoreAction_preserves_left (g : pResidual 2 firstParabolic)
    (q : core) (hq : q ∈ coreQuaternionData.left) :
    residualCoreAction g q ∈ coreQuaternionData.left := by
  change (residualCoreAction g q : M12) ∈ leftFactor
  rw [residualCoreAction_apply]
  exact (Subgroup.mem_normalizer_iff.mp
    (firstParabolic_normalizes_left g.val.property) q.val).mp hq

theorem residualCoreAction_preserves_right (g : pResidual 2 firstParabolic)
    (q : core) (hq : q ∈ coreQuaternionData.right) :
    residualCoreAction g q ∈ coreQuaternionData.right := by
  change (residualCoreAction g q : M12) ∈ rightFactor
  rw [residualCoreAction_apply]
  exact (Subgroup.mem_normalizer_iff.mp
    (firstParabolic_normalizes_right g.val.property) q.val).mp hq

private theorem firstParabolic_normalizes_left_image :
    firstParabolic ≤ Subgroup.normalizer
      (coreQuaternionData.left.map core.subtype : Set M12) := by
  rw [leftFactor_core_image]
  exact firstParabolic_normalizes_left

private theorem firstParabolic_normalizes_right_image :
    firstParabolic ≤ Subgroup.normalizer
      (coreQuaternionData.right.map core.subtype : Set M12) := by
  rw [rightFactor_core_image]
  exact firstParabolic_normalizes_right

def residualLeftAction : pResidual 2 firstParabolic →*
    MulAut (coreQuaternionData.left.map core.subtype) :=
  (coreQuaternionData.left.map core.subtype).normalizerMonoidHom.comp
    ((Subgroup.inclusion (by exact firstParabolic_normalizes_left_image)).comp
      (pResidual 2 firstParabolic).subtype)

def residualRightAction : pResidual 2 firstParabolic →*
    MulAut (coreQuaternionData.right.map core.subtype) :=
  (coreQuaternionData.right.map core.subtype).normalizerMonoidHom.comp
    ((Subgroup.inclusion (by exact firstParabolic_normalizes_right_image)).comp
      (pResidual 2 firstParabolic).subtype)

theorem residualLeftAction_apply (g : pResidual 2 firstParabolic)
    (q : coreQuaternionData.left.map core.subtype) :
    (residualLeftAction g q : M12) = (g.val : M12) * q * (g.val : M12)⁻¹ := rfl

theorem residualRightAction_apply (g : pResidual 2 firstParabolic)
    (q : coreQuaternionData.right.map core.subtype) :
    (residualRightAction g q : M12) = (g.val : M12) * q * (g.val : M12)⁻¹ := rfl

def residualCubic : pResidual 2 firstParabolic :=
  ⟨⟨cubicActor,cubicActor_mem⟩,cubicActor_residual⟩

theorem residualCubic_coe : (residualCubic.val : M12) = cubicActor := rfl

theorem residualCoreAction_cubic (q : core) :
    (residualCoreAction residualCubic q : M12) = cubicActor * q * cubicActor⁻¹ := rfl

theorem residualLeftAction_cubic :
    residualLeftAction residualCubic = localCubic.actionLeft := rfl

theorem residualRightAction_cubic :
    residualRightAction residualCubic = localCubic.actionRight := rfl

theorem residualLeftAction_cubic_ne_one : residualLeftAction residualCubic ≠ 1 := by
  rw [residualLeftAction_cubic]
  exact localCubic.actionLeft_ne_one

theorem residualRightAction_cubic_ne_one : residualRightAction residualCubic ≠ 1 := by
  rw [residualRightAction_cubic]
  exact localCubic.actionRight_ne_one

end Sporadic.Mathieu.M12SmallPair

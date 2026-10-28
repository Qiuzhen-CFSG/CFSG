module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core.Quaternion
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Core.Centralizer

/-!
# Self-centralizing two-core in the generated ternary involution local group

The product of the two concrete quaternion images is a normal two-subgroup
of `generated`. Any element centralizing its two-core centralizes those
quaternion generators, hence is the identity or the marked involution by the
faithful octonion-frame calculation. Both elements lie in the quaternion
subgroup and therefore in the two-core.

This proves the intrinsic core-centralizer condition without assuming an
order or generation theorem for the full involution centralizer. Normality
is relative to `generated`, not to the ambient G₂ model.

Source application: Aschbacher–Smith, I.4(G1), printed p.417, and Main Theorem
0.1.2(4), pp.3–4 (also pp.481–482). See Core.Action for coordinate attribution.
-/

public section

namespace Atlas.G2.TernaryLocals.Involution
open CoreCalculation

/-- The concrete root-generated subgroup of the involution centralizer has
self-centralizing two-core. No centralizer-order or generation premise is used. -/
theorem generated_centralizer_pCore :
    Subgroup.centralizer (pCore 2 generated : Set generated) ≤ pCore 2 generated := by
  intro g hg
  have hcomm := Subgroup.mem_centralizer_iff.mp hg
  have hi (s : Bool) : quaternionI s * g.val = g.val * quaternionI s := by
    have hq : (⟨quaternionI s, quaternionI_mem s⟩ : generated) ∈ intrinsicQuaternion :=
      quaternionI_mem_subgroup s
    exact congrArg Subtype.val (hcomm _ (intrinsicQuaternion_le_pCore hq))
  have hj (s : Bool) : quaternionJ s * g.val = g.val * quaternionJ s := by
    have hq : (⟨quaternionJ s, quaternionJ_mem s⟩ : generated) ∈ intrinsicQuaternion :=
      quaternionJ_mem_subgroup s
    exact congrArg Subtype.val (hcomm _ (intrinsicQuaternion_le_pCore hq))
  apply intrinsicQuaternion_le_pCore
  change g.val ∈ quaternionSubgroup
  rcases centralizer_quaternion_generators g.val hi hj with he | he
  · rw [he]
    exact quaternionSubgroup.one_mem
  · rw [he]
    exact centralSign_mem_subgroup

end Atlas.G2.TernaryLocals.Involution

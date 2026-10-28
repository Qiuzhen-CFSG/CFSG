module

public import Theory.GroupAction.HomomorphismFixingAutomorphisms
public import Theory.GroupTheory.PGroup.UniqueInvolutionAutomorphisms
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# Normalizer actions on two-subgroups of GL₂

The determinant-one part of a two-subgroup has at most one involution: the
actual two-by-two matrix calculation identifies every such involution with
`-I`. Hence this part is cyclic or generalized quaternion, and its automorphism
group is a {2,3}-group. For an elementary abelian subgroup it is cyclic, so its
automorphism group is a two-group. Conjugation preserves every determinant
value. The displacement argument for automorphisms preserving a homomorphism
shows that restricting this action to the determinant kernel has two-group
kernel. These observations prove the two normalizer-action bounds.

Source: Aschbacher–Smith A.1.26, printed pp.25–26. This direct determinant
argument proves the two calculations attributed there to Dickson's theorem;
it retains the scalar involution and uses actual matrix inclusions throughout.
-/

open Subgroup

namespace Matrix.GeneralLinearGroup
variable {F : Type*} [Field F]

private theorem detKernel_involution (hF : (2 : F) ≠ 0)
    (V : Subgroup (GL (Fin 2) F))
    (x : (det.comp V.subtype).ker) (hx : orderOf x = 2) : x.val.val = -1 := by
  have hs : x.val.val ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg (fun a : (det.comp V.subtype).ker => a.val.val) h
  rcases eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF x.val.val hs x.property with h | h
  · have he : x = 1 := Subtype.ext (Subtype.ext h)
    simp [he] at hx
  · exact h

private theorem detKernel_involutions_eq (hF : (2 : F) ≠ 0)
    (V : Subgroup (GL (Fin 2) F))
    (x y : (det.comp V.subtype).ker) (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  exact Subtype.ext (Subtype.ext ((detKernel_involution hF V x hx).trans
    (detKernel_involution hF V y hy).symm))

private theorem normalizerAction_le_fixingDet (V : Subgroup (GL (Fin 2) F)) :
    V.normalizerMonoidHom.range ≤ (det.comp V.subtype).fixingAut := by
  rintro a ⟨n, rfl⟩ x
  change det (n.val * x.val * n.val⁻¹) = det x.val
  rw [map_mul, map_mul, map_inv]
  simp

/-- The automorphisms induced by the normalizer of an elementary abelian
two-subgroup of GL₂ in odd characteristic form a two-group. -/
public theorem normalizerAction_isPGroup_of_elementaryAbelian_two [Finite F]
    (hF : (2 : F) ≠ 0) (V : Subgroup (GL (Fin 2) F)) [IsElementaryAbelian 2 V] :
    IsPGroup 2 V.normalizerMonoidHom.range := by
  let d := det.comp V.subtype
  have hK : IsPGroup 2 d.ker := (IsElementaryAbelian.isPGroup 2 V).to_subgroup d.ker
  have : IsCyclic d.ker := hK.isCyclic_of_involutions_eq (detKernel_involutions_eq hF V)
  exact (d.isPGroup_fixingAut hK hK.mulAut_of_isCyclic_two).of_injective
    (Subgroup.inclusion (normalizerAction_le_fixingDet V))
    (Subgroup.inclusion_injective _)

/-- The automorphisms induced by the normalizer of a two-subgroup of GL₂
in odd characteristic form a {2,3}-group. -/
public theorem normalizerAction_isPiGroup_of_isPGroup_two [Finite F]
    (hF : (2 : F) ≠ 0) (V : Subgroup (GL (Fin 2) F)) (hV : IsPGroup 2 V) :
    IsPiGroup twoThreePrimes V.normalizerMonoidHom.range := by
  let d := det.comp V.subtype
  have hK : IsPGroup 2 d.ker := hV.to_subgroup d.ker
  have hA := hK.isPiGroup_mulAut_of_involutions_eq (detKernel_involutions_eq hF V)
  exact (d.isPiGroup_fixingAut (p := 2) (by left; rfl) hK hA).of_injective
    (Subgroup.inclusion (normalizerAction_le_fixingDet V))
    (Subgroup.inclusion_injective _)
end Matrix.GeneralLinearGroup

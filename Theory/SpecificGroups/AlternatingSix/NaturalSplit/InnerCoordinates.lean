module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Marked
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# Inner automorphism coordinates of the natural A6 block

Under the deleted-module model of the automorphism group, the permutation
coordinate of conjugation by an element of the block is its original A6
coordinate. The same projection detects the pointwise translation fixer.
These identities give the literal parity and kernel markings used when the
original source20 normalizer is identified with the full automorphism group.

Source: Aschbacher–Smith 14.3.19(10) and the first paragraph of 14.3.20.
-/

public noncomputable section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
variable (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)

theorem automorphismHom_restriction (x:AutomorphismModel) :
    restriction (automorphismHom x)=naturalMulAction (Fin 6) x.right := by
  change restriction (kernelHom x.left * diagonal x.right)=_
  rw [map_mul,kernelHom_restriction,one_mul,restriction_diagonal]

theorem automorphismEquiv_restriction (a:MulAut Model) :
    restriction a=naturalMulAction (Fin 6) (automorphismEquiv hN a).right := by
  have h := automorphismHom_restriction (automorphismEquiv hN a)
  have he : automorphismHom (automorphismEquiv hN a)=a :=
    (automorphismEquiv hN).symm_apply_apply a
  rwa [he] at h

theorem restriction_conj (x:Model) : restriction (MulAut.conj x)=action x.right := by
  apply MulEquiv.ext
  intro v
  apply inl_injective (φ:=action)
  rw [restriction_apply]
  exact Representation.OneCohomology.split_conjugate_inl action x v

theorem automorphismEquiv_conj_right (x:Model) :
    (automorphismEquiv hN (MulAut.conj x)).right=x.right.val := by
  apply symmetric_action_injective
  exact (automorphismEquiv_restriction hN _).symm.trans (restriction_conj x)

theorem automorphismEquiv_right_eq_one (a:MulAut Model) :
    (automorphismEquiv hN a).right=1 ↔ a∈pointwiseKernel := by
  rw [←restriction_ker]
  change _ ↔ restriction a=1
  rw [automorphismEquiv_restriction hN,←map_one (naturalMulAction (Fin 6))]
  exact symmetric_action_injective.eq_iff.symm
end BinaryPermutation.SixNaturalSplit

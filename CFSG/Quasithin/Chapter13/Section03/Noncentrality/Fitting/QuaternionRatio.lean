module
public import Theory.Representation.AffineNine.QuaternionSource
public import Theory.Representation.NormalElementaryQuotient
/-!
# The literal reduced-action ratio in 13.3.14(d)

The action is the actual conjugation representation of H/C_H(W) on the
normal elementary binary subgroup W. Once the preceding source reductions
produce its normal nine-group image, the two-group image of T and the marked
quaternion automizer, its trivial two-core forces cubic ratio greater than two.
The subgroup W can therefore be the original R₂(PT); neither its quotient map
nor its action is replaced by an unmarked affine model.

The earlier source owner constructs the surviving nine-group and quaternion
image from the selected Ξ-minus subgroup and proves the two-core calculation.
The competing ratio bound from 3.1.8 remains with that original-source assembly.
Source: Aschbacher--Smith 13.3.14(d), printed p.892; direct replacement for the
particular D.2.17 obstruction used there.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

theorem quaternion_reduced_action_ratio
    (H : Subgroup G) (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (D S : Subgroup (H ⧸ centralizer (W : Set H)))
    [D.Normal] [IsElementaryAbelian 3 D]
    (hD : Nat.card D=9) (hS : IsPGroup 2 S) (hgen : D ⊔ S=⊤)
    (hcore : pCore 2 (H ⧸ centralizer (W : Set H))=⊥)
    (Q : Subgroup (MulAut D)) (eQ : Q ≃* QuaternionGroup 2)
    (hQ : Q ≤ ((MulAut.conjNormal : H ⧸ centralizer (W : Set H) →* MulAut D).comp S.subtype).range) :
    2 < BinaryOffender.cubicRatio (D := H ⧸ centralizer (W : Set H)) (V := Additive W)
      (NormalElementaryQuotient.representation W
        (QuotientGroup.mk' (centralizer (W : Set H)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  exact AffineNine.cubicRatio_gt_two_of_twoCore_eq_bot (V := Additive W) D S hD hS hgen hcore Q eQ hQ
    _ (NormalElementaryQuotient.representation_injective W _ _ _)
end CFSG.Quasithin.Chapter13.Section03.Noncentrality

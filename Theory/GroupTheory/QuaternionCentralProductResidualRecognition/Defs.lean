module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.PResidual.Defs
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Theory.PGroupCore

/-!
# Embedded data for quaternion residual recognition

The local cubic witness records its conjugation on each actual quaternion
factor. The recognition conclusion records actual SL2(3) subgroups of the
ambient group, their two-cores and common center, and their exact residual
join. Thus neither the witness nor the embeddings are replaced by abstract
order or isomorphism assertions.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace Subgroup

/-- An explicit local cubic acting nontrivially on both embedded quaternion factors. -/
public structure QuaternionLocalCubic
    {G : Type*} [Group G] (Q H : Subgroup G) (d : QuaternionCentralProductData Q) where
  element : H
  order : orderOf (element : G) = 3
  actionLeft : MulAut (d.left.map Q.subtype)
  actionRight : MulAut (d.right.map Q.subtype)
  actionLeft_apply : ∀ b : d.left.map Q.subtype,
    (actionLeft b : G) = element * b * (element : G)⁻¹
  actionRight_apply : ∀ c : d.right.map Q.subtype,
    (actionRight c : G) = element * c * (element : G)⁻¹
  actionLeft_ne_one : actionLeft ≠ 1
  actionRight_ne_one : actionRight ≠ 1

/-- The enlarged residual as an embedded central product, retaining its two-cores. -/
public structure QuaternionResidualCentralProduct
    {G : Type*} [Group G] (Q : Subgroup G) (d : QuaternionCentralProductData Q) where
  left : Subgroup G
  right : Subgroup G
  left_model : Nonempty (left ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  right_model : Nonempty (right ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  left_contains : d.left.map Q.subtype ≤ left
  right_contains : d.right.map Q.subtype ≤ right
  left_core : (pCore 2 left).map left.subtype = d.left.map Q.subtype
  right_core : (pCore 2 right).map right.subtype = d.right.map Q.subtype
  commute : ∀ l ∈ left, ∀ r ∈ right, l * r = r * l
  intersection : left ⊓ right = (center Q).map Q.subtype
  span : left ⊔ right = pResidual 2 G

end Subgroup

module
public import Theory.Representation.CentralizerQuotientAction
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus

/-!
# Exact orthogonal coordinates and ambient point centralizers

Equivariance for the original centralizer quotient identifies its model
point stabilizer with the centralizer of the original group element.
The injective ambient map retains the original subgroup representatives.
This is the transport used for Y = O²(C_H(v₂)) in Aschbacher–Smith 10.2.1,
printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent

variable {H : Type*} [Group H]

theorem orthogonal_action_fixed_iff
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (S : Subrepresentation (centralizerQuotient U))
    (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (ew : (H ⧸ centralizer (U : Set H)) ≃* BinaryFourPlus.Wreath)
    (hw : ∀ x v, c (S.toRepresentation x v) =
      (BinaryFourPlus.wreathToIsometry (ew x)).val (c v))
    (h : H) (v : S.toSubmodule) :
    (BinaryFourPlus.wreathToIsometry (ew (QuotientGroup.mk' (centralizer (U : Set H)) h))).val
      (c v) = c v ↔ h ∈ centralizer ({(v.val.toMul : H)} : Set H) := by
  rw [← hw, c.injective.eq_iff]
  have hf : S.toRepresentation (QuotientGroup.mk' (centralizer (U : Set H)) h) v = v ↔
      h * (v.val.toMul : H) * h⁻¹ = (v.val.toMul : H) := by
    constructor
    · intro he
      exact congrArg (fun w : S.toSubmodule => (w.val.toMul : H)) he
    · intro he
      apply Subtype.ext
      exact Additive.toMul.injective (Subtype.ext he)
  rw [hf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]


/-- Exact equivariance on the original normal subgroup identifies the model
point stabilizer with the ambient element centralizer. -/
theorem orthogonal_ambient_action_fixed_iff
    {G : Type*} [Group G] (j : H →* G) (hj : Function.Injective j)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (S : Subrepresentation (centralizerQuotient U))
    (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (ew : (H ⧸ centralizer (U : Set H)) ≃* BinaryFourPlus.Wreath)
    (hw : ∀ x v, c (S.toRepresentation x v) =
      (BinaryFourPlus.wreathToIsometry (ew x)).val (c v))
    (h : H) (v : S.toSubmodule) :
    (BinaryFourPlus.wreathToIsometry (ew (QuotientGroup.mk' (centralizer (U : Set H)) h))).val
      (c v) = c v ↔ j h ∈ centralizer ({j (v.val.toMul : H)} : Set G) := by
  rw [orthogonal_action_fixed_iff U S c ew hw h v]
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro he
    simpa only [map_mul] using congrArg j he
  · intro he
    apply hj
    simpa only [map_mul] using he

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent

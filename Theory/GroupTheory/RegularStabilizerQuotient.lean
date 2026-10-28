module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-!
# A stabilizer quotient and the ambient two-point stabilizer

Let G act on Ω and let Q be a normal subgroup of the stabilizer of α. If Q
acts freely and transitively on Ω minus α, then the quotient of the stabilizer
of α by Q is isomorphic to the intersection of the stabilizers of α and any
other point β. No finiteness or double transitivity is needed for this bridge.

Regularity makes Q complementary to the stabilizer of β inside the stabilizer
of α, by Mathlib's `Subgroup.isComplement'_stabilizer`. Normality then gives the
quotient isomorphism through `Subgroup.IsComplement'.QuotientMulEquiv`. Finally,
the identity on underlying group elements identifies the nested stabilizer
with the ambient intersection. All actions are the inherited actions on
`SubMulAction.ofStabilizer`, so dependent constructions share their instances.

This elementary consequence of the Mathlib complement results translates
quotient data to two-point-stabilizer data in permutation-group recognition,
in particular from Alperin–Brauer–Gorenstein Theorem C(iv) to the hypotheses
of O’Nan's unitary-group characterization. It uses no recognition theorem.
-/

namespace MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- A normal subgroup acting regularly away from α has stabilizer quotient
isomorphic to the ambient stabilizer of α and β. -/
public theorem nonempty_stabilizer_quotient_equiv_inf_of_regular
    (α : Ω) (Q : Subgroup (stabilizer G α)) [Q.Normal]
    [IsCancelSMul Q (SubMulAction.ofStabilizer G α)]
    [IsPretransitive Q (SubMulAction.ofStabilizer G α)]
    (β : SubMulAction.ofStabilizer G α) :
    Nonempty ((stabilizer G α) ⧸ Q ≃* ↥(stabilizer G α ⊓ stabilizer G (β : Ω))) := by
  let e : (stabilizer G α) ⧸ Q ≃* stabilizer (stabilizer G α) β :=
    (Subgroup.isComplement'_stabilizer β
      (fun _ h ↦ IsCancelSMul.eq_one_of_smul h)
      (fun g ↦ exists_smul_eq Q (g • β) β)).symm.QuotientMulEquiv
  let f : stabilizer (stabilizer G α) β ≃*
      ↥(stabilizer G α ⊓ stabilizer G (β : Ω)) :=
    { toFun := fun x ↦ ⟨x.val.val, x.val.property,
        congrArg Subtype.val (show x.val • β = β from x.property)⟩
      invFun := fun x ↦ ⟨⟨x.val, x.property.1⟩, Subtype.ext x.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  exact ⟨e.trans f⟩

end MulAction

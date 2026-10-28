module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Faithful conjugation on the binary derived group

Every nontrivial normal subgroup of the actual octonion group G₂(2)
contains its derived subgroup H. If the kernel of conjugation on H were
nontrivial, H would therefore centralize itself. But H is perfect and has
order 6048, so it cannot be abelian. This proves faithfulness without any
assumption about the order or structure of its automorphism group.

Source: the automorphism identification used in Aschbacher--Smith F.1.12,
printed pp.263--264, and Definition F.4.3, printed p.274. The underlying
normal-generation and root calculations are the licensed ATLAS port and
its checked extensions, cited in the imports. Surjectivity remains a
separate obligation.
-/

public section

namespace Atlas.G2.LieAutomorphismExtensions

/-- Full-group conjugation acts faithfully on the actual binary commutator. -/
theorem binaryConjugation_injective : Function.Injective binaryConjugation := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hn
  have hHK := BinaryException.H_le_normal binaryConjugation.ker hn
  let : Group.IsPerfect BinaryException.H := BinaryException.H_isPerfect
  let : IsMulCommutative BinaryException.H := ⟨⟨fun x y => by
    apply Subtype.ext
    have hx : binaryConjugation x.val = 1 := hHK x.property
    let yD : BinaryDerived := ⟨y.val, binaryDerived_eq.symm ▸ y.property⟩
    have hy := congrArg (fun a : MulAut BinaryDerived => (a yD).val) hx
    change x.val * y.val * x.val⁻¹ = y.val at hy
    exact mul_inv_eq_iff_eq_mul.mp hy⟩⟩
  let : Subsingleton BinaryException.H := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hc : Nat.card BinaryException.H = 1 := Nat.card_unique
  rw [BinaryException.card_H] at hc
  contradiction

end Atlas.G2.LieAutomorphismExtensions

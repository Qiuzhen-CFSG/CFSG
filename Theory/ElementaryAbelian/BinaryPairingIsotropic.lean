module
public import Theory.ElementaryAbelian.BinaryPairingCardinality
public import Theory.ElementaryAbelian.Injective

/-!
# Isotropic subgroup orders for binary pairings

For a left-nondegenerate pairing on a finite elementary abelian two-group,
an isotropic subgroup has squared order at most the ambient order. Restrict
the first variable to the subgroup and use the cardinality of the resulting
right kernel. Symmetry or alternation of the pairing is not required.

The natural small-index argument uses this bound for its commutator pairing.
-/

open scoped IsMulCommutative
namespace MonoidHom

/-- An isotropic subgroup of a finite binary pairing has order at most the
square root of the ambient order. Only left nondegeneracy is needed. -/
public theorem binary_pairing_isotropic_card_sq_le
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (f : V →* (V →* Multiplicative (ZMod 2))) (hinj : Function.Injective f)
    (S : Subgroup V)
    (hzero : ∀ x ∈ S, ∀ y ∈ S, f x y = 1) :
    (Nat.card S)^2 ≤ Nat.card V := by
  let fS := f.comp S.subtype
  let : IsElementaryAbelian 2 S :=
    IsElementaryAbelian.of_injective S.subtype S.subtype_injective
  have hS : S ≤ fS.flip.ker := by
    intro y hy
    apply MonoidHom.mem_ker.mpr
    ext x
    change f x.val y = 1
    exact hzero x.val x.property y hy
  calc
    (Nat.card S)^2 = Nat.card S * Nat.card S := pow_two _
    _ ≤ Nat.card S * Nat.card fS.flip.ker :=
      Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hS)
    _ = Nat.card V :=
      binary_pairing_card_mul_card_ker_flip fS (hinj.comp S.subtype_injective)

end MonoidHom

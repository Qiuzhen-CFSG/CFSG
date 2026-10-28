module
public import Theory.ElementaryAbelian.BinaryPairingDuality

/-!
# Cardinalities for nondegenerate binary pairings

A pairing of finite elementary abelian two-groups which is nondegenerate
in its first argument maps the second group onto the dual of the first.
Thus the order of the first group times the order of the right kernel is
the order of the second group. The proof uses finite linear duality over
`ZMod 2`; equal dimensions are not required.
-/

open scoped IsMulCommutative
namespace MonoidHom

/-- A finite binary group and its binary dual have the same order. -/
public theorem binary_dual_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] :
    Nat.card (A →* Multiplicative (ZMod 2)) = Nat.card A := by
  let e : (A →* Multiplicative (ZMod 2)) ≃ (Additive A →ₗ[ZMod 2] ZMod 2) := {
    toFun f := (MonoidHom.toAdditiveLeft f).toZModLinearMap 2
    invFun f := MonoidHom.toAdditiveLeft.symm f.toAddMonoidHom
    left_inv f := rfl
    right_inv f := by ext a; rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)]
  rfl

/-- Left nondegeneracy of a finite binary pairing gives right surjectivity. -/
public theorem binary_pairing_flip_surjective
    {A B : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group B] [Finite B] [IsElementaryAbelian 2 B]
    (f : A →* (B →* Multiplicative (ZMod 2)))
    (hinj : Function.Injective f) : Function.Surjective f.flip := by
  let pairing : Additive A →+ (Additive B →ₗ[ZMod 2] ZMod 2) := {
    toFun a := (MonoidHom.toAdditiveLeft (f a.toMul)).toZModLinearMap 2
    map_zero' := by ext b; change (f 1 b.toMul).toAdd = 0; simp
    map_add' a b := by
      ext x
      change (f (a.toMul * b.toMul) x.toMul).toAdd =
        (f a.toMul x.toMul).toAdd + (f b.toMul x.toMul).toAdd
      rw [map_mul]
      rfl }
  let linearPairing := pairing.toZModLinearMap 2
  have hlinj : Function.Injective linearPairing := by
    intro a b hab
    apply Additive.toMul.injective
    apply hinj
    ext x
    apply Multiplicative.toAdd.injective
    exact congrArg (fun l : Additive B →ₗ[ZMod 2] ZMod 2 => l (Additive.ofMul x)) hab
  have hsurj : Function.Surjective linearPairing.flip :=
    LinearMap.flip_surjective_iff₁.mpr hlinj
  intro l
  obtain ⟨b, hb⟩ := hsurj ((MonoidHom.toAdditiveLeft l).toZModLinearMap 2)
  refine ⟨b.toMul, ?_⟩
  ext a
  apply Multiplicative.toAdd.injective
  exact congrArg (fun t : Additive A →ₗ[ZMod 2] ZMod 2 => t (Additive.ofMul a)) hb

/-- The right kernel has the order prescribed by left nondegeneracy. -/
public theorem binary_pairing_card_mul_card_ker_flip
    {A B : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group B] [Finite B] [IsElementaryAbelian 2 B]
    (f : A →* (B →* Multiplicative (ZMod 2))) (hinj : Function.Injective f) :
    Nat.card A * Nat.card f.flip.ker = Nat.card B := by
  have hc := f.flip.ker.index_mul_card
  rw [Subgroup.index_ker, f.flip.range_eq_top.mpr (binary_pairing_flip_surjective f hinj),
    Subgroup.card_top, binary_dual_card] at hc
  exact hc

end MonoidHom

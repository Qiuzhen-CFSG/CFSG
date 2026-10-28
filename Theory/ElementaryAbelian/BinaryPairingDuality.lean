module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Duality for finite binary group pairings

Let A and B be finite elementary abelian two-groups of equal order. If the
supplied pairing A → Hom(B,C₂) is injective, its flipped homomorphism
B → Hom(A,C₂) is bijective. The target is the literal multiplicative group
of ZMod2; neither the pairing nor either group is replaced by coordinates.

Additive type tags turn the exact pairing into a ZMod2 bilinear map. The
finite dual of B has the same cardinality as B, so the left injection is
bijective. The standard linear-dual flip theorem gives the right bijection,
which transports back through the same type-tag conversions.

This source-neutral finite duality supplies the perfect commutator pairing
for the terminal core supplement in Stellmacher (10.1), Journal of Algebra
190 (1997), printed p.65, immediately after (20).
-/

open scoped IsMulCommutative
namespace MonoidHom

public theorem binary_pairing_flip_bijective
    {A B : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group B] [Finite B] [IsElementaryAbelian 2 B]
    (f : A →* (B →* Multiplicative (ZMod 2)))
    (hcard : Nat.card A=Nat.card B) (hinj : Function.Injective f) :
    Function.Bijective f.flip := by
  classical
  let pairing : Additive A →+ (Additive B →ₗ[ZMod 2] ZMod 2) := {
    toFun := fun a => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft (f a.toMul))
    map_zero' := by
      ext b
      change (f 1 b.toMul).toAdd=0
      simp
    map_add' := by
      intro a b
      ext x
      change (f (a.toMul*b.toMul) x.toMul).toAdd=
        (f a.toMul x.toMul).toAdd+(f b.toMul x.toMul).toAdd
      rw [map_mul]
      rfl }
  let linearPairing := pairing.toZModLinearMap 2
  let _ : Finite (Additive B →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f : Additive B →ₗ[ZMod 2] ZMod 2 => (f : Additive B → ZMod 2))
      DFunLike.coe_injective
  have hlinj : Function.Injective linearPairing := by
    intro a b hab
    apply Additive.toMul.injective
    apply hinj
    ext x
    apply Multiplicative.toAdd.injective
    exact congrArg (fun l : Additive B →ₗ[ZMod 2] ZMod 2 => l (Additive.ofMul x)) hab
  have hdualcard : Nat.card (Additive B →ₗ[ZMod 2] ZMod 2)=Nat.card (Additive A) := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Subspace.dual_finrank_eq,
      ←Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive B)]
    exact hcard.symm
  have hflip : Function.Bijective linearPairing.flip :=
    LinearMap.flip_bijective_iff₁.mpr (hlinj.bijective_of_nat_card_le hdualcard.le)
  constructor
  · intro b c hbc
    apply Additive.ofMul.injective
    apply hflip.1
    ext a
    exact congrArg (fun l : A →* Multiplicative (ZMod 2) => (l a.toMul).toAdd) hbc
  · intro l
    let linear := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft l)
    obtain ⟨b,hb⟩ := hflip.2 linear
    refine ⟨b.toMul,?_⟩
    ext a
    apply Multiplicative.toAdd.injective
    exact congrArg (fun t : Additive A →ₗ[ZMod 2] ZMod 2 => t (Additive.ofMul a)) hb

end MonoidHom

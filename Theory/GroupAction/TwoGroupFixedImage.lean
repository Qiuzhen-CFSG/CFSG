module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

/-!
# Fixed images under a two-group action

For an equivariant homomorphism with finite source and odd kernel, the
image of the fixed subgroup is exactly the fixed subgroup in the image.
The supplied actions and homomorphism are retained literally. The subgroup
corollary applies this to an invariant odd subgroup of the source.

A nonempty fiber is in bijection with the kernel. Over a fixed image point,
that fiber is stable under the actor. Its odd cardinality and the two-group
orbit-counting theorem therefore supply a fixed representative. This needs
neither solvability nor surjectivity of the homomorphism.

This is the coprime fixed-point step in Kurzweil–Stellmacher, *The Theory of
Finite Groups*, §11.1.3, printed pp.306–307. The lower-layer formulation is
independent of the signalizer application.
-/

namespace MonoidHom

private def kernelEquivFiber {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) : f.ker ≃ {z : G // f z = f x} where
  toFun n := ⟨x * n, by simp [f.mem_ker.mp n.property]⟩
  invFun z := ⟨x⁻¹ * z, by simp [mem_ker, z.property]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

public theorem map_fixedPoints_eq_of_odd_kernel
    {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G] [MulDistribMulAction A H]
    (hA : IsPGroup 2 A) (f : G →* H) (hker : Odd (Nat.card f.ker))
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (FixedPoints.subgroup A G).map f = f.range ⊓ FixedPoints.subgroup A H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun a => (hequiv a x).symm.trans (congrArg f (hx a))⟩
  · rintro y ⟨⟨x, rfl⟩, hfix⟩
    let Fiber := {z : G // f z = f x}
    have hodd : Odd (Nat.card Fiber) := by
      rwa [Nat.card_congr (kernelEquivFiber f x).symm]
    let : MulAction A Fiber :=
      { smul := fun a z => ⟨a • z.val, by rw [hequiv, z.property, hfix a]⟩
        one_smul := fun z => Subtype.ext (one_smul A z.val)
        mul_smul := fun a b z => Subtype.ext (mul_smul a b z.val) }
    have hnot : ¬ 2 ∣ Nat.card Fiber := by
      simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hodd
    obtain ⟨z, hz⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Fiber hnot
    exact ⟨z.val, fun a => congrArg Subtype.val (hz a), z.property⟩

end MonoidHom

namespace Subgroup

public theorem map_inf_fixedPoints_eq_of_odd
    {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G] [MulDistribMulAction A H]
    (hA : IsPGroup 2 A) (f : G →* H)
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g)
    (U : Subgroup G) [IsInvariant A G U] (hU : Odd (Nat.card U)) :
    (U ⊓ FixedPoints.subgroup A G).map f = U.map f ⊓ FixedPoints.subgroup A H := by
  let r := f.comp U.subtype
  have hker : Odd (Nat.card r.ker) :=
    hU.of_dvd_nat (card_subgroup_dvd_card r.ker)
  have h := r.map_fixedPoints_eq_of_odd_kernel hA hker (fun a g => hequiv a g)
  have hrange : r.range = U.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at h
  rw [← h]
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hx⟩, rfl⟩
    exact ⟨⟨x, hxU⟩, fun a => Subtype.ext (hx a), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x.property, fun a => congrArg Subtype.val (hx a)⟩, rfl⟩

end Subgroup

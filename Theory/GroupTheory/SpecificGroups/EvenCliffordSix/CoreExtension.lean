module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Frattini
public import Mathlib.GroupTheory.Index

/-!
# Marked central extensions of the six-letter augmentation core

This interface records an order-two central kernel, the literal augmentation
projection and its alternating action. A lift of the constant vector has square
equal to the nonidentity kernel element. These are input data for recognizing
the group of even signed monomials; the interface assumes neither an abstract
group isomorphism nor a comparison with the signed action.

The actual quartic hexad construction supplies these data by reducing its
cyclic-four center modulo squares and applying binary-cover recognition.
Source: Aschbacher–Smith I.2.2(6), printed p.412.
-/

@[expose] public section
namespace EvenCliffordSix

/-- Elementary marked extension data, before group or action recognition. -/
structure CoreExtension (G : Type*) [Group G] where
  projection : G →* Multiplicative V
  surjective : Function.Surjective projection
  sign : G
  sign_order : orderOf sign = 2
  kernel : projection.ker = Subgroup.zpowers sign
  sign_central : sign ∈ Subgroup.center G
  actor : A →* MulAut G
  equivariant : ∀ a x, (projection (actor a x)).toAdd =
    BinaryPermutation.coreRepresentation (Fin 6) a.val (projection x).toAdd
  volume : G
  volume_central : volume ∈ Subgroup.center G
  volume_projection : projection volume = Multiplicative.ofAdd volumeVector
  volume_square : volume ^ 2 = sign

namespace CoreExtension
variable {G : Type*} [Group G] (d : CoreExtension G)
include d

theorem kernel_card : Nat.card d.projection.ker = 2 := by
  rw [d.kernel, Nat.card_zpowers, d.sign_order]

theorem kernel_central : d.projection.ker ≤ Subgroup.center G := by
  rw [d.kernel]
  exact Subgroup.zpowers_le.mpr d.sign_central

/-- Every square belongs to the specified central binary kernel. -/
theorem square_mem_kernel (x : G) : x ^ 2 ∈ d.projection.ker := by
  rw [MonoidHom.mem_ker, map_pow, pow_two]
  change (d.projection x).toAdd + (d.projection x).toAdd = 0
  apply Subtype.ext
  funext i
  exact CharTwo.add_self_eq_zero ((d.projection x).toAdd.val i)

/-- The kernel and quotient determine the group order. -/
theorem card : Nat.card G = 64 := by
  have hc : d.projection.ker.index = 32 := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        d.projection d.surjective).toEquiv]
    change Nat.card V = 32
    rw [Module.natCard_eq_pow_finrank (K := F), BinaryPermutation.finrank_core]
    norm_num [F]
  have h := d.projection.ker.card_mul_index
  rw [d.kernel_card, hc] at h
  exact h.symm

theorem isPGroup : IsPGroup 2 G := IsPGroup.of_card (n := 6) d.card

/-- The volume square makes the central kernel exactly Frattini. -/
theorem frattini_eq_kernel [Finite G] : frattini G = d.projection.ker := by
  rw [d.isPGroup.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact d.square_mem_kernel x
  · rw [d.kernel]
    apply Subgroup.zpowers_le.mpr
    rw [← d.volume_square]
    exact Subgroup.subset_closure ⟨d.volume, rfl⟩

end CoreExtension
end EvenCliffordSix

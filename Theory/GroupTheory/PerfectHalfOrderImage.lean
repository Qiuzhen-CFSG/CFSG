module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Uniqueness of a perfect subgroup of half the ambient order

If a finite group has order at most twice the order of a perfect subgroup,
that subgroup is the unique subgroup of its order. Every other subgroup of
that order has index one or two, so its abelian quotient kills the perfect
subgroup. The resulting image comparison retains the literal homomorphisms.

The U₄(2) recognition uses this with the faithful native image of order 25920
in the automorphism group of the 27-point quadrangle, whose order is at most
51840. Perfectness of the group being recognized is not required.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.PerfectHalfOrderImage
variable {A G K : Type*} [Group A] [Group G] [Group K]

/-- An index at most two subgroup contains the ambient commutator subgroup. -/
theorem commutator_le_of_index_le_two (H : Subgroup A) [Finite A]
    (h : H.index ≤ 2) : commutator A ≤ H := by
  have hp : 0 < H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
  have hc : H.index = 1 ∨ H.index = 2 := by omega
  rcases hc with hc | hc
  · rw [Subgroup.index_eq_one.mp hc]
    exact le_top
  · let : H.Normal := H.normal_of_index_eq_two hc
    have : IsCyclic (A ⧸ H) := isCyclic_of_prime_card hc
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- The perfect subgroup is determined just by its order and the ambient bound. -/
theorem subgroup_eq (H J : Subgroup A) [Finite A] [Group.IsPerfect H]
    (hcard : Nat.card J = Nat.card H) (hbound : Nat.card A ≤ 2 * Nat.card H) : J = H := by
  have hidx : J.index ≤ 2 := by
    have hp : 0 < Nat.card J := Nat.card_pos
    have he := J.index_mul_card
    rw [← hcard] at hbound
    nlinarith
  have hle : H ≤ J := by
    calc
      H = ⁅H, H⁆ := H.commutator_eq_self.symm
      _ ≤ commutator A := Subgroup.commutator_mono le_top le_top
      _ ≤ J := commutator_le_of_index_le_two J hidx
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

/-- The literal images of two faithful representations of the same order agree. -/
theorem range_eq [Finite A] [Finite G] [Finite K] [Group.IsPerfect K]
    (f : G →* A) (k : K →* A) (hf : Function.Injective f) (hk : Function.Injective k)
    (hcard : Nat.card G = Nat.card K) (hbound : Nat.card A ≤ 2 * Nat.card K) :
    f.range = k.range := by
  have : Group.IsPerfect k.range := Group.IsPerfect.range k
  have hcG : Nat.card f.range = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hcK : Nat.card k.range = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hk).toEquiv).symm
  exact subgroup_eq k.range f.range (hcG.trans (hcard.trans hcK.symm))
    (by rwa [hcK])

/-- The image comparison induces an isomorphism, with its homomorphism equation retained. -/
def equivOfRangeEq (f : G →* A) (k : K →* A)
    (hf : Function.Injective f) (hk : Function.Injective k) (he : f.range = k.range) : G ≃* K :=
  (MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr he).trans
    (MonoidHom.ofInjective hk).symm)

@[simp] theorem equivOfRangeEq_apply (f : G →* A) (k : K →* A)
    (hf : Function.Injective f) (hk : Function.Injective k) (he : f.range = k.range) (g : G) :
    k (equivOfRangeEq f k hf hk he g) = f g := by
  change ((MonoidHom.ofInjective hk)
    ((MonoidHom.ofInjective hk).symm ((MulEquiv.subgroupCongr he)
      ((MonoidHom.ofInjective hf) g))) : A) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end Theory.GroupTheory.PerfectHalfOrderImage

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki

/-!
# Involution commutators in the quintic local models

Every involution in D₁₀ or in the literal matrix group Sz(2) has a commutator
of order five. For D₁₀ the rotation generator is a witness. For Sz(2), the
existing equivalence with a five-normalizer in S₅ reduces the assertion to
its self-centralizing subgroup of order five: an involution cannot centralize
that subgroup, and a nontrivial commutator inside it has order five.

The final theorem transports both models to an arbitrary specified group.
It supplies the finite-model input to the critical-core escape argument in
Aschbacher--Smith 14.6.12; no representation or module marking is assumed.
-/

public section
open Subgroup
open scoped commutatorElement

namespace Subgroup

private theorem exists_prime_order_commutator_of_not_centralizing {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p) (t : G)
    (ht : t ∈ normalizer (P : Set G)) (hn : t ∉ centralizer (P : Set G)) :
    ∃ x ∈ P, orderOf (t * x * t⁻¹ * x⁻¹) = p := by
  classical
  have hn' : ¬ ∀ x ∈ P, x * t = t * x := by
    intro h
    exact hn (mem_centralizer_iff.mpr h)
  push Not at hn'
  obtain ⟨x,hx,hnx⟩ := hn'
  refine ⟨x,hx,?_⟩
  have hc : t * x * t⁻¹ * x⁻¹ ∈ P :=
    P.mul_mem ((mem_normalizer_iff.mp ht x).mp hx) (P.inv_mem hx)
  have hd : orderOf (t * x * t⁻¹ * x⁻¹) ∣ p :=
    hP ▸ P.orderOf_dvd_natCard hc
  apply orderOf_eq_prime_iff.mpr
  refine ⟨orderOf_dvd_iff_pow_eq_one.mp hd,?_⟩
  intro he
  exact hnx (commutatorElement_eq_one_iff_mul_comm.mp he).symm

end Subgroup

namespace DihedralGroup
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
/-- Every involution in D₁₀ has an order-five commutator with the rotation generator. -/
theorem exists_order_five_commutator_of_involution (t : DihedralGroup 5) (ht : orderOf t = 2) :
    ∃ x : DihedralGroup 5, orderOf (t * x * t⁻¹ * x⁻¹) = 5 := by
  have hf : ∀ y : DihedralGroup 5, y ^ 2 = 1 → y ≠ 1 →
      (y * r 1 * y⁻¹ * (r 1)⁻¹) ^ 5 = 1 ∧
      y * r 1 * y⁻¹ * (r 1)⁻¹ ≠ 1 := by decide +kernel
  have ht' := (orderOf_eq_prime_iff (p := 2)).mp ht
  exact ⟨r 1, orderOf_eq_prime_iff.mpr (hf t ht'.1 ht'.2)⟩
end DihedralGroup

namespace Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Involutions in a five-normalizer have a commutator of order five. -/
theorem exists_order_five_commutator_of_involution (P : Sylow 5 D) (t : normalizer ((P : Subgroup D) : Set D))
    (ht : orderOf t = 2) :
    ∃ x : normalizer ((P : Subgroup D) : Set D),
      orderOf (t * x * t⁻¹ * x⁻¹) = 5 := by
  have htn : t.val ∉ centralizer ((P : Subgroup D) : Set D) := by
    intro hc
    rw [centralizer_eq P] at hc
    have hd := (P : Subgroup D).orderOf_dvd_natCard hc
    rw [card_sylow P, orderOf_coe t, ht] at hd
    norm_num at hd
  obtain ⟨x,hx,ho⟩ := (P : Subgroup D).exists_prime_order_commutator_of_not_centralizing
    (card_sylow P) t.val t.property htn
  let y : normalizer ((P : Subgroup D) : Set D) :=
    ⟨x,(P : Subgroup D).le_normalizer hx⟩
  refine ⟨y,?_⟩
  exact (orderOf_coe (t*y*t⁻¹*y⁻¹)).symm.trans ho

end Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups

namespace BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups

/-- The literal matrix Sz(2) model has an order-five commutator at every involution. -/
theorem suzukiZero_exists_order_five_commutator_of_involution
    (t : SuzukiMatrixGroup 0) (ht : orderOf t = 2) :
    ∃ x : SuzukiMatrixGroup 0, orderOf (t*x*t⁻¹*x⁻¹) = 5 := by
  let P : Sylow 5 D := Classical.choice inferInstance
  obtain ⟨e⟩ := normalizer_equiv_suzuki P
  have he : orderOf (e.symm t) = 2 := (e.symm.orderOf_eq t).trans ht
  obtain ⟨x,hx⟩ := exists_order_five_commutator_of_involution P (e.symm t) he
  refine ⟨e x,?_⟩
  have ho := (e.orderOf_eq (e.symm t*x*(e.symm t)⁻¹*x⁻¹)).trans hx
  simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply] using ho
end BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups

/-- The original D₁₀/Sz(2) quotient marking supplies an order-five commutator. -/
theorem exists_order_five_commutator_of_quintic_model
    {G : Type*} [Group G]
    (hG : Nonempty (G ≃* DihedralGroup 5) ∨
      Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (t : G) (ht : orderOf t = 2) : ∃ x : G, orderOf (t*x*t⁻¹*x⁻¹) = 5 := by
  rcases hG with hG | hG
  · obtain ⟨e⟩ := hG
    obtain ⟨x,hx⟩ := DihedralGroup.exists_order_five_commutator_of_involution (e t)
      ((e.orderOf_eq t).trans ht)
    refine ⟨e.symm x,?_⟩
    have ho := (e.symm.orderOf_eq (e t*x*(e t)⁻¹*x⁻¹)).trans hx
    simpa only [map_mul,map_inv,MulEquiv.symm_apply_apply] using ho
  · obtain ⟨e⟩ := hG
    obtain ⟨x,hx⟩ := BenderSuzuki.MatrixGroups.suzukiZero_exists_order_five_commutator_of_involution (e t)
      ((e.orderOf_eq t).trans ht)
    refine ⟨e.symm x,?_⟩
    have ho := (e.symm.orderOf_eq (e t*x*(e t)⁻¹*x⁻¹)).trans hx
    simpa only [map_mul,map_inv,MulEquiv.symm_apply_apply] using ho
end Theory.SpecificGroups

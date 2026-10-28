module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Central commutators and literal conjugacy cosets

For a in P, if [⟨a⟩,P] centralizes P, the commutator map on P is a
homomorphism whose image is exactly [⟨a⟩,P]. Powers in the first argument
prove the image equality, without assuming that subgroup generators already
exhaust the subgroup. This identifies the conjugacy orbit with a[⟨a⟩,P]
and identifies the source subgroup product with the corresponding join.

Source application: Aschbacher–Smith, 15.3.61(2), printed p.1150.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion
variable {G : Type*} [Group G]

private def centralCommutatorHom (P : Subgroup G) (a : G)
    (hC : ⁅zpowers a, P⁆ ≤ centralizer (P : Set G)) : P →* G where
  toFun p := ⁅a, (p : G)⁆
  map_one' := by simp
  map_mul' p q := by
    change ⁅a, (p : G) * q⁆ = ⁅a, (p : G)⁆ * ⁅a, (q : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc := hC (commutator_mem_commutator (mem_zpowers a) q.property) p p.property
    calc
      _ = ⁅a, (p : G)⁆ * ((p : G) * ⁅a, (q : G)⁆) * (p : G)⁻¹ := by group
      _ = _ := by rw [hc]; group

private theorem centralCommutatorHom_range (P : Subgroup G) (a : G) (ha : a ∈ P)
    (hC : ⁅zpowers a, P⁆ ≤ centralizer (P : Set G)) :
    (centralCommutatorHom P a hC).range = ⁅zpowers a, P⁆ := by
  have hAP : zpowers a ≤ P := zpowers_le.mpr ha
  have hCP : ⁅zpowers a, P⁆ ≤ P := commutator_le.mpr
    (fun x hx y hy => P.mul_mem (P.mul_mem (P.mul_mem (hAP hx) hy)
      (P.inv_mem (hAP hx))) (P.inv_mem hy))
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact commutator_mem_commutator (mem_zpowers a) p.property
  · apply commutator_le.mpr
    intro x hx p hp
    let g : zpowers a →* G := {
      toFun := fun x => ⁅(x : G), p⁆
      map_one' := by simp
      map_mul' := by
        intro x y
        change ⁅(x : G) * (y : G), p⁆ = ⁅(x : G), p⁆ * ⁅(y : G), p⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hy := commutator_mem_commutator y.property hp
        rw [hC hy x (hAP x.property), mul_inv_cancel_right]
        exact hC (commutator_mem_commutator x.property hp) _ (hCP hy) }
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨(⟨p, hp⟩ : P) ^ n, ?_⟩
    rw [map_zpow]
    exact (g.map_zpow (⟨a, mem_zpowers a⟩ : zpowers a) n).symm

/-- With central commutators, the actual conjugacy orbit is the literal coset. -/
theorem conjugate_iff_mem_commutator_coset (P : Subgroup G) (a : G) (ha : a ∈ P)
    (hC : ⁅zpowers a, P⁆ ≤ centralizer (P : Set G)) (x : G) :
    (∃ p ∈ P, MulAut.conj p a = x) ↔ ∃ c ∈ ⁅zpowers a, P⁆, a * c = x := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hc : ⁅p, a⁆ ∈ ⁅zpowers a, P⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hp (mem_zpowers a)
    refine ⟨⁅p, a⁆, hc, ?_⟩
    rw [conj_eq_commutatorElement_mul]
    exact hC hc a ha
  · rintro ⟨c, hc, rfl⟩
    have hr : c⁻¹ ∈ (centralCommutatorHom P a hC).range := by
      rw [centralCommutatorHom_range P a ha hC]
      exact inv_mem hc
    obtain ⟨p, hp⟩ := hr
    have he : ⁅(p : G), a⁆ = c := by
      have h := congrArg Inv.inv hp
      simpa only [centralCommutatorHom, MonoidHom.coe_mk, OneHom.coe_mk,
        commutatorElement_inv, inv_inv] using h
    refine ⟨p, p.property, ?_⟩
    rw [conj_eq_commutatorElement_mul, he]
    exact (hC hc a ha).symm

/-- Centrality makes conjugation transitive on every point of the coset. -/
theorem commutator_coset_transitive (P : Subgroup G) (a : G) (ha : a ∈ P)
    (hC : ⁅zpowers a, P⁆ ≤ centralizer (P : Set G)) :
    ∀ c₁ ∈ ⁅zpowers a, P⁆, ∀ c₂ ∈ ⁅zpowers a, P⁆,
      ∃ p ∈ P, MulAut.conj p (a * c₁) = a * c₂ := by
  intro c₁ hc₁ c₂ hc₂
  obtain ⟨p, hp, he⟩ := (conjugate_iff_mem_commutator_coset P a ha hC
    (a * (c₂ * c₁⁻¹))).mpr ⟨_, mul_mem hc₂ (inv_mem hc₁), rfl⟩
  refine ⟨p, hp, ?_⟩
  have hf : MulAut.conj p c₁ = c₁ := by
    change p * c₁ * p⁻¹ = c₁
    rw [hC hc₁ p hp, mul_inv_cancel_right]
  rw [map_mul, he, hf]
  group

/-- The subgroup notation in the source is its setwise product. -/
theorem cyclic_commutator_sup_eq_product (P : Subgroup G) (a : G) (ha : a ∈ P)
    (hC : ⁅zpowers a, P⁆ ≤ centralizer (P : Set G)) :
    ((zpowers a ⊔ ⁅zpowers a, P⁆ : Subgroup G) : Set G) =
      (zpowers a : Set G) * (⁅zpowers a, P⁆ : Subgroup G) := by
  apply coe_mul_of_left_le_normalizer_right
  apply zpowers_le.mpr
  apply Subgroup.centralizer_le_normalizer
  intro c hc
  exact (hC hc a ha).symm
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion

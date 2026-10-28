module
public import Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Multiplicity estimates from separated alternating-five supports

The two projected elementary ranks account for all of a faithful actor.
For each invariant block, a rank-one projection supplies a nonidentity
involution and a rank-two projection supplies a nonidentity inner involution.
The corresponding displacement estimates give at least k times the projected
rank. Fixed codimensions add on the two actual blocks. An actor exchanging
blocks instead moves a whole block and has rank at most three.

The numerical consequence k ≤ 2 is the separated-support input in the A₅
specialization of Aschbacher–Smith D.3.9 and D.3.21. The concrete homogeneous
module coordinates and their displacement estimates remain explicit inputs.
-/

public section
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender
namespace Representation.AlternatingFive.SeparatedActorRank
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
open Representation.BinaryOffender.NaturalTensor
variable {A V W U : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

omit [Finite A] in
/-- One invariant block pays its multiplicity times the projected actor rank. -/
theorem projected_rank_mul_le_fixedCodim
    (ρ : Representation (ZMod 2) A V) (f : A →* Sym) (k : ℕ)
    (hnontrivial : ∀ a : A, f a ≠ 1 → k ≤ operatorFixedCodim (ρ a))
    (hinner : ∀ a : A, f a ≠ 1 → f a ∈ Alt →
      2 * k ≤ operatorFixedCodim (ρ a)) :
    k * primeRank 2 f.range ≤ fixedCodim ρ ⊤ := by
  have hr := range_rank_le_two f
  by_cases hzero : primeRank 2 f.range = 0
  · simp only [hzero, mul_zero, Nat.zero_le]
  by_cases htwo : primeRank 2 f.range = 2
  · obtain ⟨a, ha, he⟩ := exists_nontrivial_even_image f htwo.ge
    have hh := (hinner a ha he).trans (operatorFixedCodim_le_fixedCodim ρ ⊤ (mem_top a))
    simpa only [htwo, Nat.mul_comm k 2] using hh
  · have hone : primeRank 2 f.range = 1 := by omega
    obtain ⟨a, ha⟩ := exists_nontrivial_image f (by omega)
    have hh := (hnontrivial a ha).trans (operatorFixedCodim_le_fixedCodim ρ ⊤ (mem_top a))
    simpa only [hone, mul_one] using hh

/-- Two separated blocks account for the rank of the whole faithful actor. -/
theorem rank_mul_le_fixedCodim_prod
    (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A W)
    (f g : A →* Sym) (hf : Function.Injective (f.prod g)) (k : ℕ)
    (hρ : ∀ a : A, f a ≠ 1 → k ≤ operatorFixedCodim (ρ a))
    (hρi : ∀ a : A, f a ≠ 1 → f a ∈ Alt → 2 * k ≤ operatorFixedCodim (ρ a))
    (hσ : ∀ a : A, g a ≠ 1 → k ≤ operatorFixedCodim (σ a))
    (hσi : ∀ a : A, g a ≠ 1 → g a ∈ Alt → 2 * k ≤ operatorFixedCodim (σ a)) :
    k * primeRank 2 A ≤ fixedCodim (ρ.prod σ) ⊤ := by
  have h₁ := projected_rank_mul_le_fixedCodim ρ f k hρ hρi
  have h₂ := projected_rank_mul_le_fixedCodim σ g k hσ hσi
  calc
    k * primeRank 2 A ≤ k * (primeRank 2 f.range + primeRank 2 g.range) :=
      Nat.mul_le_mul_left k (rank_le_sum_ranges f g hf)
    _ = k * primeRank 2 f.range + k * primeRank 2 g.range := Nat.mul_add _ _ _
    _ ≤ fixedCodim ρ ⊤ + fixedCodim σ ⊤ := Nat.add_le_add h₁ h₂
    _ = fixedCodim (ρ.prod σ) ⊤ := (fixedCodim_prod ρ σ ⊤).symm

omit [FiniteDimensional (ZMod 2) U] in
/-- Coordinates connect the block calculation to the literal full action. -/
theorem rank_mul_le_fixedCodim_of_coordinates
    (τ : Representation (ZMod 2) A U)
    (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A W)
    (e : U ≃ₗ[ZMod 2] V × W)
    (he : ∀ a u, e (τ a u) = (ρ a (e u).1, σ a (e u).2))
    (f g : A →* Sym) (hf : Function.Injective (f.prod g)) (k : ℕ)
    (hρ : ∀ a : A, f a ≠ 1 → k ≤ operatorFixedCodim (ρ a))
    (hρi : ∀ a : A, f a ≠ 1 → f a ∈ Alt → 2 * k ≤ operatorFixedCodim (ρ a))
    (hσ : ∀ a : A, g a ≠ 1 → k ≤ operatorFixedCodim (σ a))
    (hσi : ∀ a : A, g a ≠ 1 → g a ∈ Alt → 2 * k ≤ operatorFixedCodim (σ a)) :
    k * primeRank 2 A ≤ fixedCodim τ ⊤ := by
  have hc := fixedCodim_map_equivariant τ (ρ.prod σ) (MonoidHom.id A) e he ⊤
  rw [Subgroup.map_id] at hc
  rw [hc]
  exact rank_mul_le_fixedCodim_prod ρ σ f g hf k hρ hρi hσ hσi

/-- The rank of a nontrivial finite elementary group is positive. -/
theorem primeRank_pos [Nontrivial A] : 0 < primeRank 2 A := by
  have hcard : 1 < Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hc := IsElementaryAbelian.card_eq_pow_primeRank (p := 2) A
  by_contra hn
  have hz : primeRank 2 A = 0 := by omega
  rw [hz, pow_zero] at hc
  omega

omit [FiniteDimensional (ZMod 2) U] in
/-- The small-actor inequality bounds the multiplicity on preserved blocks. -/
theorem multiplicity_le_two_of_coordinates [Nontrivial A]
    (τ : Representation (ZMod 2) A U)
    (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A W)
    (e : U ≃ₗ[ZMod 2] V × W)
    (he : ∀ a u, e (τ a u) = (ρ a (e u).1, σ a (e u).2))
    (f g : A →* Sym) (hf : Function.Injective (f.prod g)) (k : ℕ)
    (hρ : ∀ a : A, f a ≠ 1 → k ≤ operatorFixedCodim (ρ a))
    (hρi : ∀ a : A, f a ≠ 1 → f a ∈ Alt → 2 * k ≤ operatorFixedCodim (ρ a))
    (hσ : ∀ a : A, g a ≠ 1 → k ≤ operatorFixedCodim (σ a))
    (hσi : ∀ a : A, g a ≠ 1 → g a ∈ Alt → 2 * k ≤ operatorFixedCodim (σ a))
    (hsmall : fixedCodim τ ⊤ ≤ 2 * primeRank 2 A) : k ≤ 2 := by
  have hh := (rank_mul_le_fixedCodim_of_coordinates τ ρ σ e he f g hf k
    hρ hρi hσ hσi).trans hsmall
  exact Nat.le_of_mul_le_mul_right hh (primeRank_pos (A := A))

open WreathTwoElementaryRank in
/-- A swapped block of dimension 4k forces the stronger bound k ≤ 1. -/
theorem multiplicity_le_one_of_swapping
    (τ : Representation (ZMod 2) A U) (f : A →* WreathTwoElementaryRank.W Sym)
    (hf : Function.Injective f) (k : ℕ)
    (B : Submodule (ZMod 2) U) (hd : Module.finrank (ZMod 2) B = 4 * k)
    (a : A) (ha : (f a).right ≠ 1) (hB : Disjoint B (B.map (τ a)))
    (hsmall : fixedCodim τ ⊤ ≤ 2 * primeRank 2 A) : k ≤ 1 := by
  have hr := rank_le_three_of_swapping f hf ⟨a, ha⟩
  have hm := (finrank_le_operatorFixedCodim_of_disjoint (τ a) B hB).trans
    (operatorFixedCodim_le_fixedCodim τ ⊤ (mem_top a))
  rw [hd] at hm
  omega

end Representation.AlternatingFive.SeparatedActorRank

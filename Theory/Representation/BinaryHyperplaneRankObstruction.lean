module

public import Theory.LinearAlgebra.DisplacementFiltration
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.PGroup

/-!
# A two-subgroup obstruction from hyperplane displacement

If a linear map sends a hyperplane into a line, its rank is at most two.
If the line is not contained in its image, its rank is at most one. Hence a
two-subgroup satisfying the opposite involution-rank alternatives is trivial:
a nontrivial finite two-subgroup would contain an involution.

This is the linear and Cauchy step in Aschbacher--Smith, combined manuscript
of 1 March 2004, 14.4.7, printed pp.1008--1009. It requires no assumption
that every element of the two-subgroup is already involutory.
-/

public section
namespace Representation.BinaryHyperplaneRankObstruction
open Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- Hyperplane displacement into a line either has rank at most one, or
has rank at most two and contains that line. -/
theorem rank_alternative (δ : V →ₗ[F] V) (W ℓ : Submodule F V)
    (hW : finrank F (V ⧸ W) = 1) (hℓ : finrank F ℓ = 1)
    (hm : W.map δ ≤ ℓ) :
    finrank F δ.range ≤ 1 ∨ (finrank F δ.range ≤ 2 ∧ ℓ ≤ δ.range) := by
  have hr := δ.finrank_range_le_quotient_add_map W
  have hle := Submodule.finrank_mono hm
  rw [hW] at hr
  rw [hℓ] at hle
  by_cases hz : finrank F (W.map δ) = 0
  · left; omega
  · right
    have he : W.map δ = ℓ := Submodule.eq_of_le_of_finrank_eq hm (by omega)
    refine ⟨by omega, ?_⟩
    rw [← he]
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

variable {K : Type*} [Group K] [Finite K]

/-- An involution-rank dichotomy excludes every nontrivial two-subgroup with
the displayed hyperplane-to-line displacement. -/
theorem twoSubgroup_eq_bot (ρ : Representation F K V) (A : Subgroup K)
    (hA : IsPGroup 2 A) (W ℓ : Submodule F V)
    (hW : finrank F (V ⧸ W) = 1) (hℓ : finrank F ℓ = 1)
    (hm : ∀ a ∈ A, W.map (ρ a - LinearMap.id) ≤ ℓ)
    (hrank : ∀ a : K, orderOf a = 2 →
      2 < finrank F (LinearMap.range (ρ a - LinearMap.id)) ∨
        (finrank F (LinearMap.range (ρ a - LinearMap.id)) = 2 ∧
          ¬ ℓ ≤ LinearMap.range (ρ a - LinearMap.id))) : A = ⊥ := by
  by_contra hne
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := exists_ne (1 : A)
  have hdvd : 2 ∣ Nat.card A := (hA.dvd_orderOf hb).trans (orderOf_dvd_natCard b)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have ha' : orderOf (a : K) = 2 := (Subgroup.orderOf_coe a).trans ha
  have hlow := rank_alternative (ρ a - LinearMap.id) W ℓ hW hℓ (hm a a.property)
  rcases hrank a ha' with hhigh | ⟨htwo, hout⟩
  · rcases hlow with hlow | ⟨hlow, _⟩ <;> omega
  · rcases hlow with hlow | ⟨_, hin⟩
    · omega
    · exact hout hin

end Representation.BinaryHyperplaneRankObstruction

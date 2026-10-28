module
public import Theory.Representation.BinaryOffender.InvolutionRatio
/-!
# Two-subgroups fixing a binary hyperplane

In a finite binary representation with quadratic ratio greater than one,
a two-subgroup fixing a hyperplane is trivial. A nontrivial two-subgroup
would contain an involution; its cyclic subgroup would be a quadratic
rank-one offender on the same representation.

This supplies the hyperplane-centralizer step in Aschbacher--Smith,
15.1.29, printed p.1104, using the original quadratic ratio hypothesis.
-/

public section
open Subgroup Representation
open scoped ENNReal
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A two-subgroup fixing a subspace of codimension at most one is trivial. -/
theorem twoSubgroup_eq_bot_of_fixedCodim_le_one (ρ : Representation (ZMod 2) G V)
    (hq : 1 < quadraticRatio ρ) (A : Subgroup G) (hA : IsPGroup 2 A)
    (hc : fixedCodim ρ A ≤ 1) : A = ⊥ := by
  rcases hA.card_eq_or_dvd with hcard | hdiv
  · exact card_eq_one.mp hcard
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdiv
  have ha' : orderOf (a : G) = 2 := by
    rwa [← orderOf_injective A.subtype A.subtype_injective] at ha
  obtain ⟨he,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ a ha'
  have hle : fixedCodim ρ (zpowers (a : G)) ≤ 1 := by
    have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers (a : G)) := by
      intro v hv b
      exact hv ⟨b, zpowers_le.mpr a.property b.property⟩
    have hh := Submodule.finrank_mono hfix
    have := fixedCodim_add_finrank ρ A
    have := fixedCodim_add_finrank ρ (zpowers (a : G))
    omega
  have hh : quadraticRatio ρ ≤ 1 := by
    apply (quadraticRatio_le_one_iff ρ).mpr
    exact ⟨zpowers (a : G),⟨he,by omega⟩,hquad⟩
  exact (not_le_of_gt hq hh).elim
end Representation.BinaryOffender

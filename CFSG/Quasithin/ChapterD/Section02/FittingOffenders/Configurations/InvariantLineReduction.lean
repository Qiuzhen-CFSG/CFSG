module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.InvariantLineReduction.ProperFour

/-!
# The invariant-line reduction in D.2.14

The exact reduced local action supplies a noncentralized hyperplane fixed
space, and hence a cubic minimum greater than one. Every invariant
order-three line has moved dimension two or four. The proper-four
exclusion makes any four-dimensional support the whole original module;
otherwise all invariant-line supports are planes.

These are the two branches used in the final configuration construction.
No marked product decomposition or model recognition is assumed here.
The final application retains the actual local group P ⊔ A and the given
representation on its moved module.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14, printed pp.186--187, through the proper-four exclusion.
-/

public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The source invariant-line dichotomy, with all extra premises discharged. -/
theorem Reduced.fullSupport_or_smallInvariantSupports {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) : FullSupport ρ P A ∨ SmallInvariantSupports ρ P A := by
  classical
  by_cases hf : FullSupport ρ P A
  · exact Or.inl hf
  right
  intro Z hZ
  rcases h.invariant_line_dimension ρ hZ with hd | hd
  · exact hd
  · have ht := h.no_proper_four_support ρ hZ hd
    have hdim : Module.finrank (ZMod 2) V = 4 := by
      rw [ht] at hd
      simpa only [finrank_top] using hd
    exact (hf ⟨Z, hZ, ht, hdim⟩).elim

/-- Both reductions required before constructing the two marked configurations. -/
theorem Reduced.invariant_line_reduction {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) :
    (∃ B : Subgroup G, B ≤ A ∧ rank B = 1 ∧
      subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥) ∧
      (FullSupport ρ P A ∨ SmallInvariantSupports ρ P A) :=
  ⟨h.exists_moved_hyperplane ρ, h.fullSupport_or_smallInvariantSupports ρ⟩

/-- The full-support branch has the genuine cubic ratio three halves, without
an additional lower-ratio or hyperplane-witness assumption. -/
theorem Reduced.full_support_ratio {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hf : FullSupport ρ P A) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨_, _, _, hd⟩ := hf
  exact h.small_dimension_ratio ρ (h.one_lt_cubicRatio ρ) (by omega)

/-- Application on the literal local group PA, using its original core and actor.
The earlier-source owner supplies exactly Reduced on the faithful moved module. -/
theorem local_generated_invariant_line_reduction (P A : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s) :
    (∃ B : Subgroup (P ⊔ A : Subgroup G), B ≤ A.subgroupOf (P ⊔ A) ∧ rank B = 1 ∧
      subspaceCommutator σ (fixedSpace σ B) (A.subgroupOf (P ⊔ A)) ≠ ⊥) ∧
      (FullSupport σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) ∨
        SmallInvariantSupports σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A))) :=
  h.invariant_line_reduction σ

end CFSG.Quasithin.ChapterD.FittingConfigurations

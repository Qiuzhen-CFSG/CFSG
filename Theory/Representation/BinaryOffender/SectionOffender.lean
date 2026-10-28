module

public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Offenders on faithful invariant sections

A faithful image of an offender on a section is still an offender by the
fixed-codimension bound. Thompson replacement rules out strong offenders
when the image representation has quadratic ratio one. The resulting chain
of dimension equalities gives trivial action on the lower subspace and on
the quotient by the upper subspace, and the fixed-space supplement.

These are the representation-theoretic steps of Aschbacher–Smith B.1.5(8),
printed pp. 69–70. Section faithfulness and commutator generation are explicit
inputs here; the source assembly must derive them from its group hypotheses.
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem IsOffender.best_and_codim_eq_of_quadraticRatio_eq_one {A : Subgroup G}
    (hA : IsOffender ρ A) (hq : quadraticRatio ρ = 1) :
    IsBestOffender ρ A ∧ fixedCodim ρ A = rank A := by
  have hn : ¬ IsStrongFFModule ρ := by
    rw [isStrongFFModule_iff_quadraticRatio_lt_one, hq]
    exact lt_irrefl _
  have heq : fixedCodim ρ A = rank A :=
    le_antisymm hA.2 (Nat.le_of_not_gt (fun h => hn ⟨A, hA.1, h⟩))
  exact ⟨(isBestOffender_iff_of_not_strong ρ hn A).mpr ⟨hA.1, heq⟩, heq⟩

omit [Finite G] in
theorem IsOffender.on_faithful_section {A : Subgroup G} (hA : IsOffender ρ A)
    (U W : Subrepresentation ρ)
    (hfaith : ∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1) :
    IsOffender (imageRepresentation (sectionRepresentation ρ U W))
      (actionSubgroup (sectionRepresentation ρ U W) A) := by
  refine ⟨hA.1.actionSubgroup _ hfaith, ?_⟩
  rw [fixedCodim_actionSubgroup, actionSubgroup_rank _ A hfaith]
  exact (fixedCodim_section_le ρ U W A).trans hA.2

theorem IsBestOffender.section_contains_bestOffender {A : Subgroup G}
    (hA : IsBestOffender ρ A) (U W : Subrepresentation ρ)
    (hfaith : ∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1) :
    ∃ B ≤ actionSubgroup (sectionRepresentation ρ U W) A,
      IsBestOffender (imageRepresentation (sectionRepresentation ρ U W)) B :=
  ((hA.isOffender ρ).on_faithful_section ρ U W hfaith).exists_bestOffender _

/-- All linear consequences in the equality case, conditional only on section faithfulness. -/
theorem IsBestOffender.section_equality {A : Subgroup G} (hA : IsBestOffender ρ A)
    {U W : Subrepresentation ρ} (hUW : U ≤ W)
    (hfaith : ∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1)
    (hq : quadraticRatio (imageRepresentation (sectionRepresentation ρ U W)) = 1) :
    IsBestOffender (imageRepresentation (sectionRepresentation ρ U W))
        (actionSubgroup (sectionRepresentation ρ U W) A) ∧
      U.toSubmodule ≤ fixedSpace ρ A ∧
      (∀ a ∈ A, ∀ v, W.quotientRepresentation a v = v) ∧
      W.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
  obtain ⟨hbest, heq⟩ := ((hA.isOffender ρ).on_faithful_section ρ U W hfaith).best_and_codim_eq_of_quadraticRatio_eq_one _ hq
  rw [fixedCodim_actionSubgroup, actionSubgroup_rank _ A hfaith] at heq
  have hqbound := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation
    (sectionLower ρ U W) A
  change fixedCodim (sectionRepresentation ρ U W) A + _ ≤ _ at hqbound
  have hwbound := fixedCodim_subrepresentation_le ρ W A
  have hav := (hA.isOffender ρ).2
  have hzero : fixedCodim (sectionLower ρ U W).toRepresentation A = 0 := by omega
  have hspan := (fixedCodim_subrepresentation_eq_iff ρ W A).mp (by omega)
  exact ⟨hbest,
    (sectionLower_trivial_iff ρ hUW A).mp ((fixedCodim_eq_zero_iff _ A).mp hzero),
    quotient_trivial_of_sup_fixedSpace ρ W A hspan, hspan⟩

/-- The commutator-generation input promotes both centralization conclusions to `AL`. -/
theorem IsBestOffender.section_equality_sup {A L : Subgroup G} (hA : IsBestOffender ρ A)
    {U W : Subrepresentation ρ} (hUW : U ≤ W)
    (hfaith : ∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1)
    (hL : ⁅L, A⁆ = L)
    (hq : quadraticRatio (imageRepresentation (sectionRepresentation ρ U W)) = 1) :
    IsBestOffender (imageRepresentation (sectionRepresentation ρ U W))
        (actionSubgroup (sectionRepresentation ρ U W) A) ∧
      U.toSubmodule ≤ fixedSpace ρ (A ⊔ L) ∧
      (∀ g ∈ A ⊔ L, ∀ v, W.quotientRepresentation g v = v) ∧
      W.toSubmodule ⊔ fixedSpace ρ A = ⊤ := by
  obtain ⟨hbest, hU, hW, hspan⟩ := hA.section_equality ρ hUW hfaith hq
  refine ⟨hbest, ?_, trivial_sup_of_commutator_eq _ L A hL hW, hspan⟩
  have hAU : ∀ a ∈ A, ∀ u, U.toRepresentation a u = u := by
    intro a ha u
    exact Subtype.ext (hU u.property ⟨a, ha⟩)
  have hALU := trivial_sup_of_commutator_eq U.toRepresentation L A hL hAU
  intro u hu g
  exact congrArg Subtype.val (hALU g g.property ⟨u, hu⟩)

end Representation.BinaryOffender

module

public import CFSG.Quasithin.ChapterD.Section03.SourceCore
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitConsequences

/-!
# Orbit-module consequences of the original D.3.1 hypotheses

The module, the two-core and the central quotient are those in the source
setup. The seed's genuine Irr⁺ property gives commutator generation and
semisimplicity after quotienting fixed vectors; its conjugates account for
all simple types. The fixed-space orbit equality and TI implication are
proved for these same subspaces and the original action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.4(1),(3),(4),(6), printed pp.193–194. The assertions about the
restricted action on V_T and its generalized Fitting group are separate.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

namespace SourceHypotheses
variable (h : SourceHypotheses K ρ T X I)
include h

theorem full_commutator : subspaceCommutator ρ ⊤ X = ⊤ := by
  let := h.normal
  exact full_commutator_of_orbitSpan_eq_top ρ (by rw [normalizer_eq_top])
    h.seed h.generated

theorem sylowSpan_full_commutator :
    subspaceCommutator ρ (orbitSpan ρ (T : Subgroup G) I) X =
      orbitSpan ρ (T : Subgroup G) I := by
  let := h.normal
  exact orbitSpan_full_commutator ρ (by rw [normalizer_eq_top]; exact le_top) h.seed

theorem centralQuotient_semisimple :
    Representation.IsSemisimpleRepresentation (fixedQuotientRepresentation ρ X) := by
  let := h.normal
  exact fixedQuotient_semisimple_of_orbitSpan_eq_top ρ
    (by rw [normalizer_eq_top]) h.seed h.generated

/-- M acts transitively on all homogeneous components, for any simple
constituents chosen to name the components. -/
theorem homogeneous_transitive
    (A B : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hA : Representation.IsIrreducible A.toRepresentation)
    (hB : Representation.IsIrreducible B.toRepresentation) :
    ∃ g : normalizer (X : Set G), (homogeneousPart A ⊤).map
      (normalizerQuotientRepresentation ρ X g) = homogeneousPart B ⊤ := by
  let := h.normal
  have hn : (⊤ : Subgroup G) ≤ normalizer (X : Set G) := by
    rw [normalizer_eq_top]
  obtain ⟨g, he⟩ := homogeneousParts_transitive_of_orbitSpan_eq_top ρ hn
    h.seed h.generated A B hA hB
  exact ⟨⟨g.val, hn g.property⟩, he⟩

theorem fixedSpace_eq_seed_fixed_orbit :
    fixedSpace ρ X = orbitSpan ρ ⊤ (I ⊓ fixedSpace ρ X) := by
  let := h.normal
  exact fixedSpace_eq_orbitSpan_inf ρ X h.seed h.generated

theorem seed_ti (hc : I ⊓ fixedSpace ρ X = ⊥) (g : G) :
    I ⊓ I.map (ρ g) = ⊥ ∨ I.map (ρ g) = I := by
  let := h.normal
  exact ti_of_inf_fixedSpace_eq_bot ρ X h.seed hc g

end SourceHypotheses
end CFSG.Quasithin.ChapterD.Section03

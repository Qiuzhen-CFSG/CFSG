module
public import Theory.GroupTheory.ElementaryOuterSylowTransport
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowAutomorphisms

/-!
# Coordinate reduction of an elementary outer Sylow action

The chosen basis transports the original full-linear isomorphism to binary
coordinate matrices. The arbitrary-degree automorphism theorem gives the
actual inverse-transpose formula. The transported displacements still have
square one and commute, providing the precise input for the remaining
unitriangular calculation in G.10.15(3), printed p.363.

The degree conclusion below is conditional on that calculation, stated for
graph-times-inner automorphisms preserving an actual Sylow subgroup. It is
not an unconditional degree bound.
-/

@[expose] public noncomputable section
namespace BinaryLinear.ElementaryOuterSylow
open OuterCyclic Theory.GroupTheory

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Coordinates on the full linear group, induced by an actual basis. -/
def coordinateEquiv : LinearMap.GeneralLinearGroup (ZMod 2) V ≃*
    LinearGroup (Module.finrank (ZMod 2) V) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv (Module.finBasis (ZMod 2) V).equivFun).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)

/-- The remaining matrix obligation. This is a hypothesis, not a classification
assertion: an elementary displacement action in the graph coset has degree four. -/
def GraphSylowDegreeBound : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (P : Sylow 2 (LinearGroup n)) (g : LinearGroup n),
    (∀ u ∈ (P : Subgroup (LinearGroup n)),
      (graphLinear n * MulAut.conj g) u ∈ (P : Subgroup (LinearGroup n))) →
    (∀ u ∈ (P : Subgroup (LinearGroup n)),
      ((graphLinear n * MulAut.conj g) u * u⁻¹) ^ 2 = 1) →
    (∀ u ∈ (P : Subgroup (LinearGroup n)), ∀ v ∈ (P : Subgroup (LinearGroup n)),
      Commute ((graphLinear n * MulAut.conj g) u * u⁻¹)
        ((graphLinear n * MulAut.conj g) v * v⁻¹)) →
    n = 4

/-- Transport the literal action, then apply the graph-coset matrix bound.
No general automorphism-classification premise remains. -/
theorem finrank_eq_four_of_graphSylowDegreeBound
    (hgraph : GraphSylowDegreeBound) {H : Type*} [Group H] [Finite H]
    (a : ElementaryOuterSylowAction H)
    (e : H ≃* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hd : 3 ≤ Module.finrank (ZMod 2) V) : Module.finrank (ZMod 2) V = 4 := by
  let b := a.transport (e.trans coordinateEquiv)
  obtain ⟨g, hg⟩ := outer_eq_graph_inner (by omega) b.automorphism b.outer
  apply hgraph _ hd b.sylow g
  · simpa only [← hg] using b.preserves
  · simpa only [← hg] using b.displacement_sq
  · intro u hu v hv
    simpa only [← hg] using b.displacement_commute u v hu hv

end BinaryLinear.ElementaryOuterSylow

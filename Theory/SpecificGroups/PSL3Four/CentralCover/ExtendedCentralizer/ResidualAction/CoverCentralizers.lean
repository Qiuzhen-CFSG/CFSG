module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.LiftDefect
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CenterControl
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.Counting

/-!
# Centralizer bounds for the marked four-cover: assembly interface

The counting argument reduces the bounds 864 and 144 to three model facts:
the projective centralizer bound, the full action on the central four, and
one nonidentity central commutator defect. The latter two imply that the
chosen lift's defect has all four values; projective centralizer surjectivity
is therefore false in this case, despite equality of the two centralizer orders.

The theorem below is conditional. Its three model premises are not proved
here, so it does not yet establish the requested marked-cover bounds.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. The chosen graph and field representatives are preserved.
-/

public section
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- Assembly from the projective count and the actual cover-action calculations.
Every displayed model premise must be discharged for the source application. -/
theorem marked_bounds_of_model_calculations (d : Overgroup L) (n : NormalizerGeometry d)
    (hp : Nat.card (projectiveCentralizer d n.graphFieldI) ∣ 864)
    (ha : Function.Surjective (centralFourAction d n.graphFieldI))
    (hx : ∃ x, centralizerLiftDefect d n.graphFieldI x ≠ 1) :
    Nat.card (centralizerIn n.graphFieldI) ∣ 864 ∧
      Nat.card (centerCentralizerIn (L := L) n.graphFieldI) ∣ 144 := by
  have hw := n.graphField_mem_centerCentralizer
  have hc : Nat.card (centralizerIn n.graphFieldI) ∣ 864 := by
    rw [centralizer_card_eq_projective_of_defect_surjective d n.graphFieldI
      (defect_surjective_of_nontrivial d n.graphFieldI hw ha hx)]
    exact hp
  exact ⟨hc, centerCentralizer_card_dvd_of_action_surjective d n.graphFieldI hw ha hc⟩

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers

module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist.Normalization
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist.StandardCover

/-!
# A nonidentity central twist for the marked graph-field lift

The normalization theorem rechooses the projective covering map while keeping
the original group L and conjugation by the original marked product τf.
Consequently a central twist for the standard graph-field lift supplies exactly
the required twist for that product, with the same y and central z. The existing
`nontrivial_defect_of_cover_twist` then gives its projective-centralizer lift.

The standard-cover theorem proves the needed twist by root commutators and
central Sylow transfer. `marked_twist` discharges the model premise of the
retained conditional reduction, using just the marked overgroup geometry and
the supplied E₉ fixed residual. Its lifting corollaries retain the original
elements and compute the literal defect z inverse. No nontrivial defect,
centralizer order, residual-action image or simultaneous choice of standard
graph and field representatives is assumed.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
open ProjectiveFixer
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The standard-cover calculation suffices for the original marked product.
The finite assembly below discharges its explicit model premise. -/
theorem marked_twist_of_standard_twists (d : Overgroup L) (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine)
    (hstandard : ∀ (c : FourCover L) (a : MulAut L),
      (PSL3.OuterSolvable.standard F ≤ (c.toCover.autMap c.ker_eq_center).range) →
      (∀ x : L, c.toMonoidHom (a x) = graphField (c.toMonoidHom x)) →
      (∀ z : center L, a (z : L) = z) →
      (pResidual 2 a.fixedSubgroup ≃* ElementaryNine) →
      ∃ y : L, ∃ z : center L, z ≠ 1 ∧ a y = (z : L) * y) :
    ∃ y : L, ∃ z : center L, z ≠ 1 ∧
      (MulAut.conjNormal n.graphFieldI : MulAut L) y = (z : L) * y := by
  obtain ⟨_, c, _, hlift, hc⟩ := standard_cover_for_marked_action d n e
  apply hstandard c (MulAut.conjNormal n.graphFieldI) hlift hc _ e
  intro z
  apply Subtype.ext
  change n.graphFieldI * ((z : L) : I) * n.graphFieldI⁻¹ = ((z : L) : I)
  have hz : ((z : L) : I) * n.graphFieldI = n.graphFieldI * ((z : L) : I) :=
    n.graphField_mem_centerCentralizer _ (mem_map_of_mem L.subtype z.property)
  rw [← hz, mul_inv_cancel_right]

/-- The original marked graph-field action has a nonidentity central twist. -/
theorem marked_twist [Finite I] (d : Overgroup L) (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    ∃ y : L, ∃ z : center L, z ≠ 1 ∧
      (MulAut.conjNormal n.graphFieldI : MulAut L) y = (z : L) * y := by
  exact marked_twist_of_standard_twists d n e (fun c a => standard_cover_twist c a)

/-- The twist witness itself lifts the projective centralizer, with defect z inverse. -/
theorem marked_twist_with_liftDefect [Finite I] (d : Overgroup L)
    (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    ∃ y : L, ∃ z : center L, z ≠ 1 ∧
      (MulAut.conjNormal n.graphFieldI : MulAut L) y = (z : L) * y ∧
      ∃ x : projectiveCentralizerPreimage d n.graphFieldI, (x : I) = y ∧
        (centralizerLiftDefect d n.graphFieldI x : I) = (((z : L) : I))⁻¹ := by
  obtain ⟨y, z, hz, htwist⟩ := marked_twist d n e
  obtain ⟨x, hxy, hx⟩ := liftDefect_of_cover_twist d n.graphFieldI y z htwist
  exact ⟨y, z, hz, htwist, x, hxy, hx⟩

/-- The marked cover supplies the nonzero defect required by the counting argument. -/
theorem marked_nontrivial_defect [Finite I] (d : Overgroup L)
    (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    ∃ x : projectiveCentralizerPreimage d n.graphFieldI,
      centralizerLiftDefect d n.graphFieldI x ≠ 1 := by
  obtain ⟨y, z, hz, htwist⟩ := marked_twist d n e
  exact nontrivial_defect_of_cover_twist d n.graphFieldI y z hz htwist

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist

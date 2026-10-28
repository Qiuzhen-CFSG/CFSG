module

public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.SpinLift.QuarterTurns
public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.Projection
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration

/-!
# Surjectivity of the actual spin–Leech pullback

Transport a Leech isometry's binary action through the fixed source lattice
comparison and the actual central-quotient coordinates. Factor the resulting
isometry of the central square form into nonsingular symmetries, then lift each
factor by its orthogonal spin quarter turn. The product satisfies the literal
compatibility equation defining `localPullback`.

Consequently its Leech projection is surjective, and the existing tensor-kernel
descent gives an unconditional surjection from C to the Leech central quotient.
This discharges the surjectivity input of the Monster local-obstruction adapter.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.4 and Section 27,
especially the fiber product on pp. 147–149 and Lemma 27.6(2).
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Sporadic.Monster.Construction.QuasithinObstruction
open LocalC TrialitySpin LocalC.SourceNormalizer

private theorem symmetry_list_spinLift
    (as : List {v : CentralSpace // q1CentralQuadraticForm v = 1}) :
    ∃ F : spinNormalizer, ∀ x : Q1Image,
      centralVector (F.val.2 x) = as.foldr
        (fun a w => w + q1CentralQuadraticForm.polarBilin a.val w • a.val) (centralVector x) := by
  induction as with
  | nil => exact ⟨1, fun _ => rfl⟩
  | cons a as ih =>
    obtain ⟨F, hF⟩ := ih
    obtain ⟨q, hq⟩ := centralVector_surjective a.val
    have hq2 : q ^ 2 = q1ImageCenterGenerator :=
      (centralVector_square_iff q).mp (hq ▸ a.property)
    refine ⟨quarterTurnSpin q hq2 * F, ?_⟩
    intro x
    change centralVector ((quarterTurnSpin q hq2).val.2 (F.val.2 x)) = _
    rw [quarterTurnSpin_automorphism, quarterTurn_centralVector, hF, hq]
    rfl

open Atlas.Lattices

/-- Every lattice isometry has an orthogonal spin lift with exactly its binary action. -/
theorem leechIsometry_spinLift (g : LeechIsometryGroup) :
    ∃ F : spinNormalizer, ∀ x : Q1Image,
      latticeClass sourceLatticeComparison (F.val.2 x) =
        leechModTwoRepresentation g (latticeClass sourceLatticeComparison x) := by
  let e := q1CentralCoordinatesIsometry.trans sourceLatticeComparison
  let f := e.toLinearEquiv.trans ((leechModTwoRepresentation g).trans e.symm.toLinearEquiv)
  have hf (v) : q1CentralQuadraticForm (f v) = q1CentralQuadraticForm v := by
    change q1CentralQuadraticForm (e.symm (leechModTwoRepresentation g (e v))) = _
    rw [e.symm.map_app]
    exact (leechModTwoRepresentation_quadratic g (e v)).trans (e.map_app v)
  obtain ⟨as, has⟩ := q1CentralQuadraticForm_symmetry_factorization f hf
  obtain ⟨F, hF⟩ := symmetry_list_spinLift as
  refine ⟨F, fun x => ?_⟩
  change e (centralVector (F.val.2 x)) = leechModTwoRepresentation g (e (centralVector x))
  rw [hF, ← has]
  exact e.apply_symm_apply _

/-- Every integral Leech isometry is the Leech component of the actual pullback. -/
theorem pullbackLeech_surjective : Function.Surjective pullbackLeech := by
  intro g
  obtain ⟨F, hF⟩ := leechIsometry_spinLift g
  exact ⟨⟨(F, g), hF⟩, rfl⟩

/-- The fixed tensor-image local group surjects onto the lattice Conway quotient. -/
theorem cToLeechQuotient_surjective : Function.Surjective cToLeechQuotient :=
  cToLeechQuotient_surjective_of_pullback pullbackLeech_surjective

end Sporadic.Monster.Construction.QuasithinObstruction

module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.WordEvaluation.Certificates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.WordEvaluation.ParameterAction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
/-!
# The exact quadratic columns of the twelve local words

The normal-closure representation evaluates the specified conjugates after
undoing the ATLAS bridge. Its certified actions on h times the chart columns
are transported back by cancelling h, giving the published left column action.
The coordinate recurrence then says that generator i increments parameter i.
Induction on the literal word list evaluates its increasing-index product,
with the rightmost factor acting first, starting at (a - 1)e₀.

This is an unconditional finite word identity. It does not assert coordinate
restrictions for arbitrary full-kernel elements. See OrbitCover/source/README.md,
TwoCoreCentralizer/source/README.md, and Model.Data for conventions and ATLAS
attribution. GLS3 Table 5.3i, printed p.270, motivates the construction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound
namespace WordEvaluation
open OrbitCoverCoordinates
open scoped Matrix
set_option maxRecDepth 10000
attribute [local irreducible] naturalAction h hi w10 w14

private lemma bridge_naturalAction (g : localSubgroup) (v : NaturalModule) :
    toMatrix h *ᵥ naturalAction (g : involutionCentralizer) v =
      NormalClosureControl.representation g *ᵥ (toMatrix h *ᵥ v) := by
  have he : NormalClosureControl.representation g * toMatrix h =
      toMatrix h * ((g.val.val : BinaryMatrixˣ) : BinaryMatrix) := by
    change ((toAmbient h * g.val.val * (toAmbient h)⁻¹ : BinaryMatrixˣ) : BinaryMatrix) *
      (toAmbient h : BinaryMatrix) =
        (toAmbient h : BinaryMatrix) * (g.val.val : BinaryMatrix)
    rw [← Units.val_mul, ← Units.val_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [naturalAction_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he]

private lemma word_eq_conjugates {G : Type*} [Group G] (x y u t : G) (i : Fin 12) :
    (((conjugatingWords.get i).map (fun b => if b then x else y)).prod)⁻¹ * u *
      ((conjugatingWords.get i).map (fun b => if b then x else y)).prod =
        NormalClosureControl.conjugates x y u t i.succ := by
  fin_cases i <;>
    simp [conjugatingWords, NormalClosureControl.conjugates, Vector.get,
      mul_inv_rev, mul_assoc]

private lemma orbitGenerator_eq_basis (i : Fin 12) :
    orbitGenerator i = NormalClosureControl.basis i.succ :=
  word_eq_conjugates subgroupX subgroupY localSeed subgroupInvolution i

private lemma bridge_injective : Function.Injective (Matrix.mulVec (toMatrix h)) := by
  have undo (v : NaturalModule) : toMatrix h⁻¹ *ᵥ (toMatrix h *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  intro u v he
  rw [← undo u, he, undo v]

private lemma generator_synthesize (i : Fin 12) (x : Fin 22 → ZMod 2) :
    naturalAction (orbitGenerator i : involutionCentralizer) (synthesize x) =
      synthesize (coefficientAction i *ᵥ x) := by
  apply bridge_injective
  rw [bridge_naturalAction, orbitGenerator_eq_basis, NormalClosureControl.representation_basis,
    ← chart_synthesize x, ← chart_synthesize (coefficientAction i *ᵥ x), eval_h]
  simp only [Matrix.mulVec_mulVec]
  rw [generator_chart, Matrix.mul_assoc]

private lemma generator_quadraticVector (i : Fin 12) (x : Fin 12 → ZMod 2) :
    naturalAction (orbitGenerator i : involutionCentralizer) (quadraticVector x) =
      quadraticVector (x + Pi.single i 1) := by
  change naturalAction _ (synthesize (parameterCoordinates x)) =
    synthesize (parameterCoordinates (x + Pi.single i 1))
  rw [generator_synthesize, coefficientAction_parameters]

private lemma word_action
    (m : OrbitMask) (l : List (Fin 12)) (x : Fin 12 → ZMod 2) :
    naturalAction ((l.map (fun i => if m i then orbitGenerator i else 1)).prod :
      involutionCentralizer) (quadraticVector x) =
        quadraticVector (x + (l.map (fun i => Pi.single i (maskCoordinates m i))).sum) := by
  have step (i : Fin 12) (z : Fin 12 → ZMod 2) :
      naturalAction ((if m i then orbitGenerator i else 1) : localSubgroup)
        (quadraticVector z) =
          quadraticVector (z + Pi.single i (maskCoordinates m i)) := by
    cases hm : m i
    · simp [hm, maskCoordinates, map_one]
    · simpa [hm, maskCoordinates] using generator_quadraticVector i z
  induction l with
  | nil => simp [map_one]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Subgroup.coe_mul, map_mul]
    change naturalAction ((if m i then orbitGenerator i else 1) : localSubgroup)
      (naturalAction ((l.map (fun i => if m i then orbitGenerator i else 1)).prod :
        involutionCentralizer) (quadraticVector x)) = _
    rw [ih, step]
    congr 1
    abel

end WordEvaluation

open OrbitCoverCoordinates WordEvaluation

/-- The specified increasing-index word has exactly the quadratic chart column. -/
theorem representativeVector_eq_quadraticVector (m : OrbitMask) : representativeVector m = quadraticVector (maskCoordinates m) := by
  change naturalAction (orbitRepresentative m : involutionCentralizer) _ = _
  have he := word_action m (List.ofFn (fun i : Fin 12 => i)) 0
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Finset.univ_sum_single, zero_add] at he
  rw [quadraticVector_zero] at he
  exact he
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound


module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.Relations

/-!
# Elimination certificate for the mixed SL₃(4) extension bound

The checked identity `I = T P + R S` expresses every vector killed by the
sixteen relation rows S as a linear combination of the eleven template
columns T. These columns are the two published mixed formulas and the nine
section changes, with their identification checked on coordinate vectors.
Thus every normalized cocycle has the required form on the three generators.
The argument proves an upper bound and does not assume that either mixed
formula is a cocycle.

Source context: James (1973), Lemma 8.3; Aschbacher–Smith H.12.1, pp.393–394.
-/

public noncomputable section
open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion

lemma templateMatrix_eq : templateMatrix = LinearMap.toMatrix' modelInputs := by
  apply Matrix.ext
  intro u p
  rw [LinearMap.toMatrix'_apply]
  revert u
  fin_cases p <;> decide +kernel

lemma elimination_identity :
    (1 : Matrix Coord Coord F) = templateMatrix * projectionMatrix +
      recoveryMatrix * relationsMatrix := by
  decide +kernel

lemma inputs_exhausted (c : BlockCocycle .natural .dual) (hc : c.value z = 0) :
    ∃ v : Fin 11 → F, inputs c = modelInputs v := by
  refine ⟨projectionMatrix.mulVec (inputs c), ?_⟩
  have he := congrArg (fun m : Matrix Coord Coord F => m.mulVec (inputs c)) elimination_identity
  rw [Matrix.one_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, relations_vanish c hc, Matrix.mulVec_zero, add_zero,
    templateMatrix_eq, LinearMap.toMatrix'_mulVec] at he
  exact he

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion

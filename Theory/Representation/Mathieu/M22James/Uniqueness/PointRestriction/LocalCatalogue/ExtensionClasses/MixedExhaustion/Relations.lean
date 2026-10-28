module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.Data

/-!
# Checked word relations for the mixed SL₃(4) extension bound

Five short identities of actual determinant-one matrices give sixteen scalar
linear equations on the 27 cross-block entries of the three generators.
The coefficient matrix is checked on the 27 coordinate vectors. This proves
that every normalized mixed cocycle belongs to its kernel; no group
presentation or converse to these necessary relations is assumed.

Source context: James (1973), Lemma 8.3; Aschbacher–Smith H.12.1, pp.393–394.
-/

public noncomputable section
open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion

lemma relators_valid : ∀ r : Fin 5, word (leftWord r) = word (otherWord r) := by
  decide +kernel

lemma relationMatrix_eq : relationsMatrix = LinearMap.toMatrix' relationMap := by
  apply Matrix.ext
  intro r u
  rw [LinearMap.toMatrix'_apply]
  revert u
  fin_cases r <;> decide +kernel

lemma relations_vanish (c : BlockCocycle .natural .dual) (hc : c.value z = 0) :
    relationsMatrix.mulVec (inputs c) = 0 := by
  rw [relationMatrix_eq, LinearMap.toMatrix'_mulVec]
  funext r
  change (wordMap (leftWord (relationIndex r)) (inputs c) +
    wordMap (otherWord (relationIndex r)) (inputs c)) (relationRow r) (relationCol r) = 0
  rw [wordMap_value c hc, wordMap_value c hc, relators_valid]
  exact CharTwo.add_self_eq_zero _

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion

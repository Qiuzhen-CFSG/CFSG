module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.ComplementAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.AlternatingModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.MathieuModel

/-!
# Coordinates for the two split involution-centralizer models

The binary reduction preserves the actual conjugation action and identifies
its semidirect product with the input centralizer. The explicit ordinary and
parity-twisted actions give fixed targets for the remaining action classification
and the comparisons with the genuine M22 and A10 centralizers.

The local dichotomy in the remark on printed p.224 of D. Held, "A
Characterization of some multiply transitive permutation groups, I", Illinois
J. Math. 13 (1969), 224–240, DOI 10.1215/ijm/1256053756, is assembled here
from the action alternatives under the full source hypotheses and the two
concrete model equivalences. None is an assumed field in the input data or a
consequence of the coordinate change alone.
-/

namespace Theory.GroupTheory.HeldM22A10

universe u

namespace LocalModelDichotomy

variable {G : Type u} [Group G] [Finite G]

/-- The split involution centralizer is one of the two concrete local models
from Held's p.224 dichotomy. The binary reduction identifies the actual
centralizer with its coordinate semidirect product; the action alternatives
then identify that product with the corresponding twisted or ordinary model,
and the model equivalences identify those products with the genuine M22 or
A10 centralizers. -/
public theorem centralizer_model_dichotomy [IsSimpleGroup G]
    (D : LocalData G) (K : Subgroup D.centralizer)
    (hK : D.kernel.IsComplement' K) :
    Nonempty (D.centralizer ≃* CentralizerModels.m22Centralizer) ∨
      Nonempty (D.centralizer ≃* CentralizerModels.a10Centralizer) := by
  rcases action_alternatives D K hK with htwisted | hpermutation
  · rcases htwisted with ⟨e⟩
    left
    exact ⟨(D.binarySemidirectEquiv K hK).symm.trans
      (e.trans twistedModelEquivM22Centralizer)⟩
  · rcases hpermutation with ⟨e⟩
    right
    exact ⟨(D.binarySemidirectEquiv K hK).symm.trans
      (e.trans permutationModelEquivA10Centralizer)⟩

end LocalModelDichotomy
end Theory.GroupTheory.HeldM22A10

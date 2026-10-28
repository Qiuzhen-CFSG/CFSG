module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.AmbientCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.CentralizerSylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Structure

/-!
# Exclusion of Janko's Case IV

The coordinate two-group embeds as an actual ambient Sylow subgroup T,
with its first vector equal to the original central involution. Its subgroup
F = C_T(d) is elementary of order sixteen. The faithful action of N_G(F)/F
on F has the specified local eight-group as the stabilizer of the first
vector. The checked finite rigidity theorem therefore gives N_G(F) = T.
The normalizer condition then makes F Sylow in C_G(d).

Thompson transfer fuses d into H = E<a,b>, where every involution has a
T-centralizer of order at least 32. This contradicts the Sylow order sixteen
in C_G(d), excluding Case IV under the original local and simplicity
hypotheses. The finite rigidity theorem replaces the source's GL(4,2)
subgroup-structure argument; no identification with A8 is assumed.

Source: Janko, A characterization of the Mathieu simple groups, I,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- Janko's Case IV cannot occur for the actual binary complement action
under the original local hypotheses in a finite simple ambient group. -/
public theorem not_nonempty_jankoCoordinates_four
    (D : LocalData G) (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    ¬ Nonempty (JankoCoordinates (D.binaryAction K hK) .four) := by
  rintro ⟨R⟩
  exact CaseFour.false_of_automizer_rigidity D K hK R CaseFour.automizer_rigidity

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

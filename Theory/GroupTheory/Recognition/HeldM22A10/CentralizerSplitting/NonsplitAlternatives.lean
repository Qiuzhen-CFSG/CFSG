module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.QuotientAction
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions

/-!
# The complete nonsplit Held centralizer alternatives

The actual quotient action on the elementary kernel has a two-element fixed
space both for S4 and for the projected Sylow subgroup. The proved binary
action classification therefore places it in one of four cases. The extension
classifications give a complement to the specified kernel or an actual
multiplicative equivalence to one of the three generated permutation groups:
the ordinary and twisted actions give the first two nonsplit models, the
twelve-orbit action splits, and the six-orbit action gives the third model.

`nonsplitAlternatives` discharges every premise of the conditional assembly
from `LocalData` and ambient finiteness. This is the local extension step for
Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), printed p.314 (PDF p.322),
citing Held, J. Algebra 8 (1968), 436--449. The source's splitting conclusion
also requires the separate exclusions of these models in a simple ambient
group; ambient simplicity is unnecessary for the alternatives proved here.
-/

namespace Theory.GroupTheory.HeldM22A10
open LocalModelDichotomy NonsplitAlternatives
universe u

/-- Assemble the extension alternatives from the four individual action cases.
The action classification and extension comparisons are explicit inputs. -/
public theorem nonsplitAlternatives_of_action_cases
    {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (hcases : ActionEquivalent D.quotientBinaryAction permutationAction ∨
      ActionEquivalent D.quotientBinaryAction twistedAction ∨
      ActionEquivalent D.quotientBinaryAction twelveOrbitAction ∨
      ActionEquivalent D.quotientBinaryAction sixOrbitAction)
    (hpermutation : ActionEquivalent D.quotientBinaryAction permutationAction →
      (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
        Nonempty (D.centralizer ≃* NonsplitModels.First))
    (htwisted : ActionEquivalent D.quotientBinaryAction twistedAction →
      (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
        Nonempty (D.centralizer ≃* NonsplitModels.Second))
    (htwelve : ActionEquivalent D.quotientBinaryAction twelveOrbitAction →
      ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K)
    (hsix : ActionEquivalent D.quotientBinaryAction sixOrbitAction →
      (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
        Nonempty (D.centralizer ≃* NonsplitModels.Third)) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.First) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Second) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Third) := by
  rcases hcases with h | h | h | h
  · rcases hpermutation h with hK | he
    · exact Or.inl hK
    · exact Or.inr (Or.inl he)
  · rcases htwisted h with hK | he
    · exact Or.inl hK
    · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inl (htwelve h)
  · rcases hsix h with hK | he
    · exact Or.inl hK
    · exact Or.inr (Or.inr (Or.inr he))

/-- The specified elementary kernel has a complement in the actual involution
centralizer, or that centralizer is multiplicatively equivalent to one of the
three concrete nonsplit models. All action and extension premises are discharged;
this local alternative holds without assuming ambient simplicity. -/
public theorem nonsplitAlternatives
    {G : Type u} [Group G] [Finite G] (D : LocalData G) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.First) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Second) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Third) := by
  apply nonsplitAlternatives_of_action_cases D
    (ActionClassification.action_cases_of_fixed_card
      D.quotientBinaryAction D.quotientSylow
      D.quotientBinaryAction_fixed_all_card D.quotientBinaryAction_fixed_card)
  · exact StandardExtensions.permutation_alternative D
  · exact StandardExtensions.twisted_alternative D
  · exact ExtraExtensions.twelveOrbit_complement D
  · exact ExtraExtensions.sixOrbit_alternatives D

end Theory.GroupTheory.HeldM22A10

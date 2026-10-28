module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Removing the central cover in the exceptional pair cases

The precise multiplier input needed here is that the center of the
quasisimple cover is a two-group. The actual pair already has trivial
two-core, so its center is then trivial. The central-quotient isomorphism
therefore gives an isomorphism of the group itself with the named model.

These are conditional transport lemmas. They neither prove a multiplier
theorem nor replace the genuine graph-field triality carrier by the
auxiliary matrix construction. The final assembly must supply the earlier
multiplier implication as authorized in its contract.

Source: the characteristic-two cases in the proof of Aschbacher–Smith
Proposition 1.3.4, printed p.511, and the covering-group facts in I.1.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions

variable {Q : Type*} [Group Q] {S : Sylow 2 Q} {R : Subgroup Q}

/-- The existing trivial two-core kills a two-group center. -/
theorem center_eq_bot_of_two_center (h : PairInput S R)
    (hZ : IsPGroup 2 (center Q)) : center Q = ⊥ := by
  have hz : center Q ≤ pCore 2 Q := le_sSup ⟨inferInstance, hZ⟩
  rw [h.twoCore] at hz
  exact le_bot_iff.mp hz

/-- The quotient map is an actual equivalence once the multiplier input
and the pair's two-core condition make its kernel trivial. -/
noncomputable def equivCenterQuotient (h : PairInput S R)
    (hZ : IsPGroup 2 (center Q)) : Q ≃* (Q ⧸ center Q) :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_two_center h hZ)).trans
    QuotientGroup.quotientBot).symm

/-- Transfer the central-quotient G₂ identification to the actual pair group. -/
theorem g2_model_of_two_center (h : PairInput S R) (hZ : IsPGroup 2 (center Q))
    {q : ℕ} (hmodel : ClassificationModels.IsG2At (Q ⧸ center Q) q) :
    ClassificationModels.IsG2At Q q := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  exact ⟨F, hF, hfin, hcard, ⟨(equivCenterQuotient h hZ).trans e⟩⟩

/-- Transfer to the genuine D₄ graph-field elementary central quotient. -/
theorem triality_model_of_two_center (h : PairInput S R) (hZ : IsPGroup 2 (center Q))
    {q : ℕ} (hmodel : Triality.Standard.IsTrialityGroupAt q (Q ⧸ center Q)) :
    Triality.Standard.IsTrialityGroupAt q Q :=
  hmodel.of_mulEquiv (equivCenterQuotient h hZ)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions

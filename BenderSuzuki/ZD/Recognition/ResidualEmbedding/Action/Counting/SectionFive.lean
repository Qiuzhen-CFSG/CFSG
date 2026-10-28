module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Seeds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.TheoremTwo

/-!
# Distinguished Section 5 counting

The local normalizer calculation proves Proposition 5.2(a). Bender's
criterion then produces the Corollary 5.7 seeds, preserving the specified
distinguished involution and prime. They exclude the exact-two-point case;
the complementary case supplies the normalizer clauses of Theorem 2.
The source assembly below discharges every Section 5 input, retaining only
the independently proved Section 3 contract and the original hypotheses.

Source: GLS, Volume 4, Chapter 2, Section 5, printed pp. 39--42.
-/

namespace BenderSuzuki.ZD

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Theorem 2 and Corollary 5.7 from the genuine Section 3 and minimality inputs. -/
public theorem actionSectionFive_of_sectionThree
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (h3 : ActionSectionThree Z M) :
    ActionTheoremTwo Z M ∧ ActionSaturationSeeds Z M := by
  have hf := actionPrimeShareMaximalFixes_of_sectionThree h r h3
  exact ⟨actionTheoremTwo_of_sectionFive_maximalFixes h r h3 hf,
    actionSaturationSeeds_of_maximalFixes h.disconnected h3 hf⟩

end BenderSuzuki.ZD

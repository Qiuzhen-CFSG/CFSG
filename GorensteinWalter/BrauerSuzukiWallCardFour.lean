module

public import GorensteinWalter.BrauerSuzukiWallCardFourBenderSplit
public import GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseOneConclusion
public import GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwoOrder
public import GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwoConclusion
public import GorensteinWalter.BrauerSuzukiWallZassenhaus

/-!
# The order-four Brauer--Suzuki--Wall branch

Bender's two exhaustive centralizer cases give the structural conclusion
with `q = 9` or `q = 7`, and hence make the ambient group a `D`-group.
-/

namespace GorensteinWalter

universe u

/-- A Brauer--Suzuki--Wall configuration with `|K| = 4` is a `D`-group. -/
public theorem BrauerSuzukiWallHypotheses.isDGroup_of_card_K_eq_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4) :
    IsDGroup G := by
  obtain ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcase⟩ :=
    h.exists_bender_case_split_of_card_K_eq_four hk
  rcases hcase with hcaseOne | hcaseTwo
  · exact
      (brauerSuzukiWallConclusion_nonempty_of_card_K_eq_four_of_bender_case_one
        h hk ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcaseOne⟩).some.isDGroup
  · have hGcard : Nat.card G = 168 :=
      h.card_eq_168_of_card_K_eq_four_of_bender_case_two
        hk V X hV hCentV hNcard hXle hXcard hcaseTwo
    exact
      (h.conclusion_nonempty_of_card_K_eq_four_of_bender_case_two_of_card_eq_168
        hk V X hV hCentV hNcard hXle hXcard hcaseTwo hGcard).some.isDGroup

end GorensteinWalter

module

public import Stellmacher.Recognition.NormalEightSeparatedCentralizerData
public import Stellmacher.Recognition.NormalEightSeparatedCentralizerSetup
public import Stellmacher.Recognition.NormalEightSeparatedClosureEight
public import Stellmacher.Recognition.NormalEightSeparatedClosureSixteen
public import Theory.GroupTheory.PGroup.NormalEightCenterTwoElementaryBound

/-!
# Assembly of the separated centralizer factorization

The local normal closure of the four in an odd-core supplement is elementary.
An elementary-order bound reduces its order to four, eight, or sixteen.
Excluding the latter two cases makes the closure equal to the four. Separation
then turns its normalizer supplement into the required centralizer supplement.

The conditional assembly remains available separately. The final theorem
discharges all its premises: the central-omega-two elementary-order bound,
the solvable centralizer setup, and both exceptional-case exclusions. This
proves Janko–Thompson Lemma 3.1 under the separated-case hypotheses.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, pp.387–388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedCentralizers

open Subgroup NormalEightSeparatedFusion

/-- Local setup and the two exceptional-case exclusions give the factorization. -/
public theorem factorization_of_normal_closure_cases
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W)
    (hzC : z ∈ center S) (hz : orderOf z = 2) (hsep : Separated S W z)
    (hbound : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16)
    (hsetup : ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
      Nonempty (CentralizerSetup S W i))
    (height : ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
      ∀ d : CentralizerSetup S W i, Nat.card d.closure ≠ 8)
    (hsixteen : ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
      ∀ d : CentralizerSetup S W i, Nat.card d.closure ≠ 16) :
    CentralizerFactorization S W := by
  apply factorization_of_normalizer_supplement S W hW z hzW hzC hz hsep
  intro i hiW hi hiC
  obtain ⟨d⟩ := hsetup i hiW hi hiC
  have hc : Nat.card d.closure = 4 := by
    rcases d.closure_card_cases hW hiW hbound with h | h | h
    · exact h
    · exact (height i hiW hi hiC d h).elim
    · exact (hsixteen i hiW hi hiC d h).elim
  exact d.normalizer_supplement_of_card_four hW hiW hc

set_option linter.unusedVariables false in
/-- Janko–Thompson Lemma 3.1: the centralizer of each noncentral involution
of the separated normal four is supplemented by its odd core and the
centralizer of the four. The elementary-eight, noncommutativity, and quotient
image hypotheses are retained for the recognition interface; the local
factorization only needs the other displayed hypotheses. -/
public theorem factorization_of_separated
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) : CentralizerFactorization S W := by
  have hbound :=
    S.isPGroup'.elementary_card_le_sixteen_of_center_omega_two_of_unique_normal_four
      hno hZ W hW hunique
  exact factorization_of_normal_closure_cases S W hW z hzW hzC hz hsep hbound
    (exists_centralizerSetup hN S hZ hno W hW z hzC hz hsep)
    (fun i hiW hi hiC d => NormalEightSeparatedClosureEight.closure_card_ne_eight
      hns hN S W hW hZ z hzW hzC hz i hiW hi hiC hno d)
    (fun _ hiW hi hiC d => d.closure_card_ne_sixteen
      hN hW z hzW hzC hz hiW hi hiC hno hbound)

end Stellmacher.Recognition.NormalEightSeparatedCentralizers

module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Configuration
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.RankOneBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Models
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.MarkedRoot

/-!
# Native source reductions for GLS4 Chapter 2, Section 16

The selection (16A)–(16E), the literal Sylow assertion and the nonsolvability
argument are proved on the original distinguished circles. If D contains a
four-group, its odd core and the Section 3 orbit give the contradiction. In
the rank-one case an elementary eight in C_M(u) suffices; constructing that
eight is precisely the remaining use of Chapter 1, Lemma 4.10. The results
below assemble both branches at that explicit earlier-source boundary and
feed nonsolvability directly into Lemma 16.3(c).

The marked root subgroup is identified through the literal circle map.
Proposition 16.5 still requires centralizer uniqueness and the field-action
comparison; no assertion of that proposition is made here.
Source: GLS4, Chapter 2, Lemma 16.3; Chapter 1, Lemma 4.10.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Lemma 16.3 nonsolvability at its sole remaining earlier rank-theorem
input. The elementary eight is requested only in the rank-one branch. -/
public theorem source16_centralizer_nonsolvable_of_rank_three_input
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (h8 : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t) →
      ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
        E ≤ centralizer ({u} : Set G) ∧ E ≤ M) :
    ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))) := by
  have hC := residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD
  by_cases hrank : TwoRankAtLeastTwo (residualPairStabilizer M t)
  · exact involutionCentralizer_circle_nonsolvable_of_pair_twoRank h r ha ht htM hrank hu huD.1 hC
  · obtain ⟨E,hEe,hEc,hEB,hEM⟩ := h8 hrank
    let := hEe
    exact involutionCentralizer_circle_nonsolvable_of_eight_of_pair_rank_one
      h.disconnected r ha htM hrank hu huD.1 hC E hEc hEB hEM

/-- The actual solvable-centralizer exclusion in 16.3(c) follows from the
preceding source argument; only Chapter 1's elementary-eight input remains. -/
public theorem source16_solvable_centralizer_le_of_rank_three_input
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u v : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (h8 : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t) →
      ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
        E ≤ centralizer ({u} : Set G) ∧ E ≤ M)
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M)
    (hsol : Group.IsSolvable (localCircle Z (centralizer ({v} : Set G)))) :
    centralizer ({v} : Set G) ≤ M := by
  exact involutionCentralizer_le_of_solvable_circle h r ha hu huD.1
    (residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD)
    (source16_centralizer_nonsolvable_of_rank_three_input h r ha ht htM hu huD h8) hv hvM hsol

end BenderSuzuki.ZD

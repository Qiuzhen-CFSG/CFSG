module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.LocalData

/-!
# Eligibility of the local group in the contrary branch of Proposition 5.2

An odd subgroup not contained in M is nontrivial. Its normalizer is proper
by simplicity: normality would force the subgroup to be the whole group,
which contains a distinguished involution and therefore has even order.
The normalizer is not contained in M and contains the displayed distinguished
involution in M. These are precisely the three eligibility conditions of
`SimpleReduction.local_embedding`.

Source: GLS, Volume 4, Chapter 2, Proposition 4.4 and the proof of 5.2.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The normalizer in the contrary branch is a proper eligible local group.
The resulting strong embedding is inside its distinguished-generated part. -/
public theorem sectionFive_local_embedding_of_not_le
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (P : Subgroup G) (hodd : Odd (Nat.card P)) (hnot : ¬ P ≤ M)
    {s : G} (hsZ : s ∈ Z) (hsM : s ∈ M)
    (hsN : s ∈ Subgroup.normalizer (P : Set G)) :
    let N := Subgroup.normalizer (P : Set G)
    IsStronglyEmbedded ((M.comap N.subtype).comap
      (Subgroup.closure (N.subtype ⁻¹' Z)).subtype) := by
  have hproper : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases r.simple.eq_bot_or_eq_top_of_normal P hn with hbot | htop
    · exact hnot (hbot ▸ bot_le)
    · have hsP : s ∈ P := htop ▸ Subgroup.mem_top s
      have hsI := IsInvolution.subtype (h.involutions s hsZ) hsP
      have hord : orderOf (⟨s, hsP⟩ : P) = 2 :=
        orderOf_eq_prime hsI.sq_eq_one hsI.ne_one
      exact hodd.not_two_dvd_nat (hord ▸ orderOf_dvd_natCard (⟨s, hsP⟩ : P))
  exact r.local_embedding _ hproper
    (fun hNM => hnot (Subgroup.le_normalizer.trans hNM)) ⟨s, hsZ, hsN, hsM⟩

end BenderSuzuki.ZD

module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Interfaces

/-!
# Eligibility of the centralizer extension for local strong embedding

The group H = C_G(K)⟨z⟩ normalizes W = ⟨K⟩. Since W is nontrivial and is
contained in the proper subgroup M of the simple ambient group, H is proper.
In the second centralizer branch H is not contained in M and contains the
distinguished base involution. These are precisely the hypotheses needed
for local strong embedding inside the distinguished closure of H.

Source: GLS, Volume 4, Chapter 2, Proposition 4.4 and Proposition 7.4.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The centralizer extension in the second branch is a proper subgroup. -/
public theorem actionGamma_centralizer_extension_proper
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) :
    Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z ≠ ⊤ := by
  have hCeq : Subgroup.centralizer d.toTheorem4bSixA.invertedSet =
      Subgroup.centralizer (d.W : Set G) := by
    rw [← d.toTheorem4bSixA.closure_invertedSet_eq, Subgroup.centralizer_closure]
  have hHN : Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔
      Subgroup.zpowers d.z ≤ Subgroup.normalizer (d.W : Set G) := by
    apply sup_le
    · rw [hCeq]
      exact Subgroup.centralizer_le_normalizer (d.W : Set G)
    · exact Subgroup.zpowers_le.mpr d.hzNorm
  intro htop
  have hnormal : d.W.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique (htop ▸ hHN))
  rcases r.simple.eq_bot_or_eq_top_of_normal d.W hnormal with hbot | hWtop
  · exact d.hWne hbot
  · exact h.proper (top_unique (hWtop ▸ d.hWM))

/-- Proposition 4.4 applies inside the distinguished closure of H.
This is relative strong embedding, not strong embedding in G or in H. -/
public theorem actionGamma_centralizer_extension_local_embedding
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M)
    (hCnot : ¬ Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M) :
    let H := Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z
    IsStronglyEmbedded ((M.comap H.subtype).comap
      (Subgroup.closure (H.subtype ⁻¹' Z)).subtype) := by
  apply r.local_embedding
  · exact actionGamma_centralizer_extension_proper h r d
  · intro hHM
    exact hCnot (le_sup_left.trans hHM)
  · exact ⟨d.z, d.hzZ,
      (show Subgroup.zpowers d.z ≤ _ from le_sup_right) (Subgroup.mem_zpowers d.z),
      d.hzM⟩

end BenderSuzuki.ZD

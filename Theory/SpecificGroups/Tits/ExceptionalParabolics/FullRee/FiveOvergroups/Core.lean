module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Normalizer
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Generation

/-!
# The marked perfect core of the large five-overgroup

The native ATLAS recovery words prove that max4 is perfect. Transport through
the fixed derived embedding and the proved conjugacy therefore makes the
intersection of a large five-overgroup with the Tits group perfect. It is
exactly that overgroup's commutator subgroup, of index two.

This retains the concrete normal core for the remaining PSL₂(25)⁺ marking in
Aschbacher–Smith J.5.4. No abstract identification of max4 or its outer action
is assumed. The downstream source consumer applies this to the original
second coset stabilizer.
-/

public section
open Subgroup
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.FiveOvergroups

theorem max4_perfect : ⁅MinimumIndexCandidates.max4,MinimumIndexCandidates.max4⁆ =
    MinimumIndexCandidates.max4 :=
  MinimumIndexThirteen.CandidateRigidity.candidateDerived_two_eq

theorem candidate_perfect : ⁅candidate,candidate⁆ = candidate := by
  rw [candidate,← map_commutator,max4_perfect]

theorem large_intersection_marking (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    ∃ g : Atlas1600Group,
      (J ⊓ D : Subgroup R).map (MulAut.conj (atlasEmbedding g)).toMonoidHom = candidate := by
  obtain ⟨_,_,_,g,hg⟩ := large_derivedPart_conjugate J hD h25 hlarge
  refine ⟨g,?_⟩
  rw [← derivedPart_map J,map_map]
  have he : (MulAut.conj (atlasEmbedding g)).toMonoidHom.comp atlasEmbedding =
      atlasEmbedding.comp (MulAut.conj g).toMonoidHom := by
    ext x : 1
    change atlasEmbedding g * atlasEmbedding x * (atlasEmbedding g)⁻¹ =
      atlasEmbedding (g*x*g⁻¹)
    simp only [map_mul,map_inv]
  rw [he,← map_map,hg]
  rfl

theorem large_intersection_perfect (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    ⁅J ⊓ D,J ⊓ D⁆ = J ⊓ D := by
  obtain ⟨g,hg⟩ := large_intersection_marking J hD h25 hlarge
  apply map_injective (f := (MulAut.conj (atlasEmbedding g)).toMonoidHom)
    (MulAut.conj (atlasEmbedding g)).injective
  rw [map_commutator,hg,candidate_perfect]

theorem large_commutator_eq (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    ⁅J,J⁆ = J ⊓ D := by
  apply le_antisymm
  · exact le_inf (commutator_le_self J) (commutator_mono le_top le_top)
  · rw [← large_intersection_perfect J hD h25 hlarge]
    exact commutator_mono inf_le_left inf_le_left

theorem large_commutator_index (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    (commutator J).index = 2 := by
  obtain ⟨hc,hd,_,_⟩ := large_derivedPart_conjugate J hD h25 hlarge
  have hc' : Nat.card (commutator J) = 7800 := by
    rw [← card_map_of_injective J.subtype_injective,J.map_subtype_commutator,
      large_commutator_eq J hD h25 hlarge,← derivedPart_card J,hd]
  have hm := (commutator J).card_mul_index
  rw [hc',hc] at hm
  omega

theorem large_commutator_equiv (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    Nonempty (commutator J ≃* MinimumIndexCandidates.max4) := by
  obtain ⟨g,hg⟩ := large_intersection_marking J hD h25 hlarge
  exact ⟨(equivMapOfInjective (commutator J) J.subtype J.subtype_injective).trans
    ((MulEquiv.subgroupCongr (J.map_subtype_commutator.trans
      (large_commutator_eq J hD h25 hlarge))).trans
    (((MulAut.conj (atlasEmbedding g)).subgroupMap _).trans
      ((MulEquiv.subgroupCongr hg).trans
        (equivMapOfInjective MinimumIndexCandidates.max4 atlasEmbedding
          atlasEmbedding_injective).symm)))⟩
end Tits.ExceptionalParabolics.FullRee.FiveOvergroups

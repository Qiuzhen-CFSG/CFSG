module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Bounds
public import Theory.SpecificGroups.Tits.FiniteImageSimple

/-!
# A fixed normalizer for the large full-Ree five-overgroup

The simple derived group makes the normalizer of a proper order-7800
intersection avoid the derived group. The preceding bound therefore shows
that every order-15600 overgroup equals that normalizer. Transporting the
native ATLAS conjugacy identifies it with the normalizer of the fixed max4
candidate under the original Atlas embedding.

This isolates the remaining PSL₂(25)⁺ recognition in Aschbacher–Smith J.5.4
at a concrete subgroup, without assuming its abstract isomorphism type.
-/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.FiveOvergroups

def candidate : Subgroup R := MinimumIndexCandidates.max4.map atlasEmbedding

def candidateNormalizer : Subgroup R := normalizer (candidate : Set R)

theorem derivedPart_map (J : Subgroup R) :
    (derivedPart J).map atlasEmbedding = J ⊓ D := by
  rw [derivedPart,map_map]
  have he : atlasEmbedding.comp atlasDerivedEquiv.symm.toMonoidHom = D.subtype := by
    ext x : 1
    change atlasEmbedding (atlasDerivedEquiv.symm x) = x.val
    rw [← atlasDerivedEquiv_coe,MulEquiv.apply_symm_apply]
  rw [he,subgroupOf_map_subtype]

theorem normalizer_intersection (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    normalizer ((J ⊓ D : Subgroup R) : Set R) = J := by
  obtain ⟨hJ,hder,_,_⟩ := large_derivedPart_conjugate J hD h25 hlarge
  have hJN : J ≤ normalizer ((J ⊓ D : Subgroup R) : Set R) :=
    (le_inf J.le_normalizer (le_normalizer_of_normal (H := D))).trans
      inf_normalizer_le_normalizer_inf
  have hDN : ¬ D ≤ normalizer ((J ⊓ D : Subgroup R) : Set R) := by
    intro hd
    let : (J.subgroupOf D).Normal := normal_subgroupOf_iff_le_normalizer_inf.mpr hd
    have hn : (derivedPart J).Normal := Normal.map inferInstance atlasDerivedEquiv.symm.toMonoidHom
      atlasDerivedEquiv.symm.surjective
    rcases hn.eq_bot_or_eq_top with hb | ht
    · rw [hb,Subgroup.card_bot] at hder
      omega
    · exact hD ((derivedPart_top_iff J).mp ht)
  have hN := card_le (normalizer ((J ⊓ D : Subgroup R) : Set R)) hDN
    (h25.trans (card_dvd_of_le hJN))
  exact (eq_of_le_of_card_ge hJN (hJ ▸ hN)).symm

theorem large_conjugate_normalizer (J : Subgroup R) (hD : ¬ D ≤ J)
    (h25 : 25 ∣ Nat.card J) (hlarge : 15600 ≤ Nat.card J) :
    Nat.card J = 15600 ∧ ∃ g : Atlas1600Group,
      J.map (MulAut.conj (atlasEmbedding g)).toMonoidHom = candidateNormalizer := by
  obtain ⟨hc,_,_,g,hg⟩ := large_derivedPart_conjugate J hD h25 hlarge
  refine ⟨hc,g,?_⟩
  have he : (J ⊓ D : Subgroup R).map (MulAut.conj (atlasEmbedding g)).toMonoidHom =
      candidate := by
    rw [← derivedPart_map J,map_map]
    have hcomp : (MulAut.conj (atlasEmbedding g)).toMonoidHom.comp atlasEmbedding =
        atlasEmbedding.comp (MulAut.conj g).toMonoidHom := by
      ext x : 1
      change atlasEmbedding g * atlasEmbedding x * (atlasEmbedding g)⁻¹ =
        atlasEmbedding (g * x * g⁻¹)
      simp only [map_mul,map_inv]
    rw [hcomp,← map_map,hg]
    rfl
  rw [← normalizer_intersection J hD h25 hlarge]
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj (atlasEmbedding g)).bijective,he]
  rfl
end Tits.ExceptionalParabolics.FullRee.FiveOvergroups

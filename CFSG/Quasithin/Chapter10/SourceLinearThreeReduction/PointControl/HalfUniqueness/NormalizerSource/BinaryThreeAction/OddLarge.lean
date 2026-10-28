module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSwap
public import Theory.SpecificGroups.PSL2.SwappedSylowNormalizer

/-!
# Closing the p ≡ ±1 mod 8 enlargement normalizer

The full-intersection case is already proved. For the remaining index-two
intersection, the actual quotient exchanger makes its coordinate projections
equally large. The index bound forces both projections to be full Sylows.
Their self-normalization and the prime-field two-group outer automorphisms
give a two-group image for the original N_G(N_T(L)) action. Its Sylow T
induces the whole image and already normalizes the original O²(H).
The checked quotient lift therefore proves normalization of that residual.

This closes both index values in the large-congruence branch of
Aschbacher--Smith 10.2.5, printed p.748, by a direct normalizer-action
argument. No S₄ selection or Thompson-subgroup premise remains in this branch.
The p ≡ ±3 mod 8 branch remains separate.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The original residual is normalized in both large-congruence intersection cases. -/
theorem Data.normalizes_residual_of_odd_large (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 1 ∨ p % 8 = 7) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  by_cases hR : stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H
  · exact h.normalizes_residual_of_odd_full_intersection hn hs hK hp ho hm hmod hR
  obtain ⟨e,a,b,hswap⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨S,hS⟩ := h.quotient_sylow
  let U := quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)
  have hUS : U ≤ (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (inf_le_left.trans inf_le_left))
  have hi : U.relIndex (S : Subgroup (XiQuotient (enlargedResidual T L H))) ≤ 2 := by
    rw [hS]
    exact h.quotient_intersection_index hn
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hlarge : 3 < p := by have hh := hp.two_le; omega
  have h8 : 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    by_contra he
    have hh := Theory.PSL2.mod_eight_of_not_eight_dvd_card (hF ▸ ho) he
    rw [hF] at hh
    omega
  have htwo := Theory.PSL2.prime_pair_intersection_action ho hlarge hF h8 eF e S U
    hUS hi a b hswap (quotientAction T L H) h.quotientAction_preserves_intersection
  have hTN := stabilizer_normalized D hn
  apply h.normalizes_residual_of_quotientAction
  intro g
  obtain ⟨t,ht,he⟩ := SylowNormalizerAction.action_detected_on_sylow
    (T.subtype hTN) (quotientAction T L H) htwo g
  rw [←he]
  exact pCoreNormalizerAction_preserves_image 2 _ _ _
    (le_normalizer_embedded_pResidual 2 H (h.sylow_le ht))

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

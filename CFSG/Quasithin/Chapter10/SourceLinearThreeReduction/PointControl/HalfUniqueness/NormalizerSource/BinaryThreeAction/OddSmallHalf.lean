module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmall
public import Theory.SpecificGroups.PSL2.SmallSylowNormalizer
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Closing the small-congruence half-intersection branch

The kernel O₂(K) lies in the original R, so passage to K/O₂(K) preserves
its index in T∩K exactly. If that index is two, the actual exchanger makes
both coordinate projections full four-groups. Their kernel-line calculation
makes the original normalizer action a two-group. The original Sylow T
induces its entire image and already normalizes O²(H). The checked residual
lift proves normalization of that same original subgroup.

Source: Aschbacher--Smith 10.2.5, printed p.748, p congruent to ±3 modulo
eight. Only the full-intersection case remains; no radical identity is
assumed here. The source assembly is connected in OddSmallFull.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The actual two-core quotient preserves the source intersection index exactly. -/
theorem Data.quotient_intersection_relIndex (h : Data D H) :
    (quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)).relIndex
      (quotientImage (enlargedResidual T L H) (T : Subgroup G)) =
    (stabilizerIntersection T L H).relIndex
      ((T : Subgroup G) ⊓ enlargedResidual T L H) := by
  let K := enlargedResidual T L H
  let R := stabilizerIntersection T L H
  have hQR : pCore 2 K ≤ R.subgroupOf K := by
    intro x hx
    exact h.enlargedResidual_core_le_intersection (mem_map_of_mem K.subtype hx)
  have hQT : pCore 2 K ≤ (T : Subgroup G).subgroupOf K :=
    hQR.trans (subgroupOf_mono K (inf_le_left.trans inf_le_left))
  change ((R.subgroupOf K).map _).relIndex (((T : Subgroup G).subgroupOf K).map _) = _
  rw [relIndex_map_map,QuotientGroup.ker_mk',sup_of_le_left hQR,sup_of_le_left hQT,
    ←relIndex_map_map_of_injective _ _ K.subtype_injective,
    map_subgroupOf_eq_of_le (show R ≤ K from inf_le_right),subgroupOf_map_subtype]

/-- The original residual is normalized whenever the small-congruence
intersection is proper in the full Sylow intersection. -/
theorem Data.normalizes_residual_of_odd_small_half (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hR : stabilizerIntersection T L H ≠ (T : Subgroup G) ⊓ enlargedResidual T L H) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  obtain ⟨e,a,b,hswap⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨S,hS⟩ := h.quotient_sylow
  let U := quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)
  have hUS : U ≤ (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (inf_le_left.trans inf_le_left))
  have hi : U.relIndex (S : Subgroup (XiQuotient (enlargedResidual T L H))) = 2 := by
    rw [hS]
    change (quotientImage _ _).relIndex (quotientImage _ _) = 2
    rw [h.quotient_intersection_relIndex]
    have hb := h.intersection_relIndex_le_two hn
    have hz : (stabilizerIntersection T L H).relIndex
        ((T : Subgroup G) ⊓ enlargedResidual T L H) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hone : (stabilizerIntersection T L H).relIndex
        ((T : Subgroup G) ⊓ enlargedResidual T L H) ≠ 1 := by
      intro he
      exact hR (le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (relIndex_eq_one.mp he))
    omega
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hlarge : 3 < p := by
    by_contra hle
    have hp3 : p = 3 := by have htwo := hp.two_le; obtain ⟨k,hk⟩ := ho; omega
    have hperfect := Group.IsPerfect.ofSurjective (f := eF.toMonoidHom) eF.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hF.trans hp3) hperfect
  have h8 := Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)
  have htwo := Theory.PSL2.prime_pair_half_action ho hlarge hF h8 eF e S U
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

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddReduction
public import Theory.SpecificGroups.PSL2.NonabelianSylowNormalizer
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups

/-!
# Odd-prime enlargements with full stabilizer intersection

For p congruent to one or seven modulo eight, the actual normal-closure
quotient is a square of prime-field PSL₂ groups with self-normalizing
Sylow two-subgroups. When R = T ∩ K, the original normalizer preserves that
full quotient Sylow, so its action image is a two-group. The original T is
Sylow in N_G(N_T(L)); it induces the entire image and already normalizes
O²(H). Quotient normalization therefore lifts to the same original residual.

This supplies the full-intersection branch of Aschbacher--Smith 10.2.5,
printed p.748, without choosing either S₄ overgroup. It retains the actual
swapped input and quotient; the other congruence and index-two cases remain
separate obligations.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The original stabilizer normalizer preserves the actual residual when
its intersection with the odd-prime enlargement is the full Sylow intersection. -/
theorem Data.normalizes_residual_of_odd_full_intersection (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 1 ∨ p % 8 = 7)
    (hR : stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨hindex,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC hA hC hs.toSwappedInput
  have hsimple := SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  obtain ⟨eo⟩ := SwappedFactorsProof.quotient_product
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 hs.toSwappedInput hindex hsimple
  have he : Nonempty (XiQuotient (enlargedResidual T L H) ≃* XiQuotient I × XiQuotient I) :=
    hK.symm ▸ ⟨eo⟩
  obtain ⟨e⟩ := he
  obtain ⟨S,hS⟩ := h.quotient_sylow
  have hRS : quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H) =
      quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
    unfold quotientImage
    rw [hR,inf_subgroupOf_right]
  have hfix (g : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) :
      (S : Subgroup (XiQuotient (enlargedResidual T L H))).map
        (quotientAction T L H g).toMonoidHom = S := by
    rw [hS,←hRS]
    exact h.quotientAction_preserves_intersection g
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hlarge : 3 < p := by have hh := hp.two_le; omega
  have h8 : 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    by_contra he
    have hh := Theory.PSL2.mod_eight_of_not_eight_dvd_card (hF ▸ ho) he
    rw [hF] at hh
    omega
  have htwo := Theory.PSL2.prime_pair_action ho hlarge hF h8 eF e S
    (quotientAction T L H) hfix
  have hi : (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf
      (T : Subgroup G)).index = 2 := by
    rw [inf_subgroupOf_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hTN : (T : Subgroup G) ≤
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (normal_of_index_eq_two hi)
  apply h.normalizes_residual_of_quotientAction
  intro g
  obtain ⟨t,ht,he⟩ := SylowNormalizerAction.action_detected_on_sylow
    (T.subtype hTN) (quotientAction T L H) htwo g
  rw [←he]
  exact pCoreNormalizerAction_preserves_image 2 _ _ _
    (le_normalizer_embedded_pResidual 2 H (h.sylow_le ht))

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

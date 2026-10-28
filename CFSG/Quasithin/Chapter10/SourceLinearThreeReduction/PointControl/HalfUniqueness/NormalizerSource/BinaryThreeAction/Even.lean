module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Swapped
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BinaryResidual

/-!
# Closing the actual even-degree PSL₂ enlargement

The detected two conjugate components identify the literal normal-closure
quotient with two copies of its actual binary PSL₂ factor. The original
complement maps injectively to a cubic plane. The inherited rank bound,
solvable Sylow overgroup and source lower-core bound give preservation of
its join with the full quotient Sylow. Its two-residual is the image of the
original O²(H); the proved kernel-normalization theorem lifts preservation
to this same original residual. Every model-calculation premise is discharged.

Source: Aschbacher--Smith 10.2.5, printed p.748, the even-characteristic
rank-one branch of (*). The odd-prime branch remains with the same owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The full original normalizer preserves O²(H) in the even rank-one case. -/
theorem Data.normalizes_residual_of_even_swapped (h : Data D H)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
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
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput eo)
  let : IsElementaryAbelian 3 P := hpc.1
  have hep : Nonempty (P ≃* quotientImage (enlargedResidual T L H) P) := by
    change Nonempty (P ≃* (P.subgroupOf (enlargedResidual T L H)).map _)
    rw [hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  let A := quotientImage (enlargedResidual T L H) P
  let U := quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)
  obtain ⟨S,hS⟩ := h.quotient_sylow
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.of_surjective ep.toMonoidHom ep.surjective
  have hcard : Nat.card A = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hrank : primeRank 3 (XiQuotient (enlargedResidual T L H)) ≤ 2 := by
    rw [hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3 (by decide) (by decide)
  let : Group.IsSolvable (A ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) : Subgroup _) := by
    rw [hS]
    change Group.IsSolvable ((quotientImage (enlargedResidual T L H) P) ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G) : Subgroup _)
    rw [hK]
    exact
      SwappedSylow.quotient_solvable hs.toSwappedInput
  have hcore : (A ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))).pCoreIn 2 ≤ U := by
    rw [hS]
    change (quotientImage (enlargedResidual T L H) P ⊔ _).pCoreIn 2 ≤ U
    rw [h.quotient_complement_join hs.toLocalInput]
    exact h.quotient_parabolic_core_le_intersection
  have hUS : U ≤ (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (inf_le_left.trans inf_le_left))
  have hres : (pResidual 2 (A ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) : Subgroup _)).map
      (A ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))).subtype =
      quotientImage (enlargedResidual T L H) (residual H) := by
    rw [hS]
    change (pResidual 2 (quotientImage (enlargedResidual T L H) P ⊔ _ : Subgroup _)).map _ = _
    rw [h.quotient_complement_join hs.toLocalInput]
    exact h.quotient_parabolic_residual
  apply h.normalizes_residual_of_quotientAction
  intro g
  have hjoin := SwappedSylow.binary_pair_preserves_join hn hm e S A U hcard hrank hcore hUS
    (quotientAction T L H g) (h.quotientAction_preserves_intersection g)
  rw [← hres,map_embedded_pResidual,hjoin]
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

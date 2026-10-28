module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.InsideCore
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OutsideCore
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# The selected centralizing source bound for 15.1.1

Every original minimal outside local gives either the inside-core quadratic
bound or the outside-core cubic bound. In the latter case the literal
Sylow centralizer quotient embeds in the normalizer's conjugation image;
the module identification is the original subgroup inclusion. The same
actor then lies in the full M-action. The standing two-overgroup condition
supplies an actual minimal outside local, proving q-hat at most two on
V(M). The original omega-center argument also proves 15.1.9(3).

These are source prerequisites for the centralizing row of 15.1.3. Its
later D.2 classification and Section 15.2 exclusion are not assumed here.
Source: Aschbacher--Smith 15.1.1(2),15.1.9(3), pp.1083--1084,1088--1089.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The literal centralizer quotient of the original Sylow embeds in its normalizer image. -/
theorem source_outsideCore_cubicRatio_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    letI := d.module_elementary
    cubicRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
      d.module_normalized) ≤ 2 := by
  let h := source_lemma_15_1_1_1 hG T hM hH
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  let V := localModule T M
  let N := sourceNormalizer T M
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := (d.module_le_core.trans (left_core_le_sylow d)).trans hH.1.1.2
  obtain ⟨hE,hTV,hq⟩ := source_outsideCore_sylow_cubicRatio hG T hM hJ H hH hout
  let := hE
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let σ := imageRepresentation N V d.module_normalized
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* N :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict N (fun s => h.sylow_le s.property)
  let f := (actionHom N V d.module_normalized).rangeRestrict.comp i
  have hk : q.ker ≤ f.ker := by
    intro s hs
    have hsC : s ∈ (centralizer (W : Set H)).subgroupOf (S : Subgroup H) :=
      (QuotientGroup.eq_one_iff s).mp hs
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have hc := congrArg H.subtype (hsC ⟨v,hVH v.property⟩ v.property)
    change (v : G) * (s.val : G) = (s.val : G) * (v : G) at hc
    change (s.val : G) * (v : G) * (s.val : G)⁻¹ = v
    rw [←hc,mul_inv_cancel_right]
  let ψ := q.liftOfSurjective hqs ⟨f,hk⟩
  have hψ (s : (S : Subgroup H)) : ψ (q s) = f s := q.liftOfRightInverse_comp_apply _ _ _ s
  let e := subgroupOfEquivOfLe hVH
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  have he : ∀ a v, E (ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨s,rfl⟩ := hqs a
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg H.subtype
      (ChapterE.DihedralCubic.representation_apply (S : Subgroup H) W hTV q hqs
        (QuotientGroup.ker_mk' _) s v)
  have hψi : Function.Injective ψ := by
    intro a b hab
    apply ChapterE.DihedralCubic.representation_injective (S : Subgroup H) W hTV q hqs
      (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    rw [he,he,hab]
  exact cubicRatio_le_nat_of_equivariant ρ σ ψ hψi E he 2 hq.le
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The selected centralizing branch of the genuine 15.1.1(2), on the original normalizer image. -/
theorem source_centralizing_normalizer_cubicRatio_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    letI := d.module_elementary
    cubicRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
      d.module_normalized) ≤ 2 := by
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  by_cases hV : localModule T M ≤ H.pCoreIn 2
  · exact (cubicRatio_le_quadraticRatio _).trans
      (source_insideCore_quadraticRatio_le_two hG T hempty hM hH hJ hV)
  · exact source_outsideCore_cubicRatio_le_two hG T hM hH hJ hV

/-- The same bound acts on V(M), with the literal full conjugation image of M. -/
theorem source_centralizing_cubicRatio_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    cubicRatio (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) ≤ 2 := by
  have hout : Chapter3.HasMaximalOutside T M := by
    obtain ⟨L,hL,K,hK,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hLM : L = M
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hK.1 hM.1.2 hK.2
        (fun he => hne (hLM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hL.1 hM.1.2 hL.2 hLM
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  let V := localModule T M
  let N := sourceNormalizer T M
  let ρ := imageRepresentation N V d.module_normalized
  let σ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  have hi : internalActionImage N V d.module_normalized ≤
      internalActionImage M V (le_normalizer_conjugateSpanBy _ _) := by
    rintro a ⟨n,rfl⟩
    exact ⟨⟨n,n.property.1⟩,rfl⟩
  exact cubicRatio_le_nat_of_equivariant ρ σ (inclusion hi) (inclusion_injective hi)
    (LinearEquiv.refl (ZMod 2) (Additive V)) (fun _ _ => rfl) 2
    (source_centralizing_normalizer_cubicRatio_le_two hG T hempty hM hH hJ)

/-- Source 15.1.9(3): every original minimal outside local centralizes the actual central seed. -/
theorem source_centralizing_HStar_le_seed_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    H ≤ centralizer (centralInvolutions T : Set G) := by
  let h := source_lemma_15_1_1_1 hG T hM hH
  have hu : ∀ L : Subgroup G, IsMaximalTwoLocal L → sourceNormalizer T M ≤ L → L = M := by
    intro L hL hNL
    exact (lemma_A_5_7_1 hM h.sylow_le inf_le_left
      (sourceNormalizer_covers_action T hM.1.2) L hL).mp hNL
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hz
    exact h.not_residual_sylow (Chapter3.source_common_normal_knownSimple hG T)
      (sourceNormalizer_mem_H hG T hM.1).1 hu
      (h.residual_sylow_source hG hM.1.1 hu hJ hz)
  intro g hg z hz
  obtain ⟨z,hzc,rfl⟩ := hZ hz
  exact congrArg H.subtype (mem_center_iff.mp hzc ⟨g,hg⟩).symm
end CFSG.Quasithin.Chapter15.Section01


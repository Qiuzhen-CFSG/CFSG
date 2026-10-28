module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OutsideCore
public import Theory.Representation.BinaryOffender.CubicRatio.Monotonicity
public import CFSG.Quasithin.ChapterD.Section01.SourceElementary

/-!
# Core containment in the ratio-two branch of 15.1.11

An outside local two-core gives a strict cubic-ratio bound through the actual
Sylow centralizer quotient. Its faithful embedding into the whole M-action
preserves strictness. Thus a cubic ratio at least two places the original
V(M) in every outside local two-core. The corresponding conjugate spans
are elementary by the actual non-FF conjugate-pair theorem.

This proves the ratio-two branch on the original V(M). The source's separate
ratio-three-halves branch uses the reselected four-dimensional Ω support and
the E.2.17 classification; neither that case nor a full 15.1.11 is asserted here.
Source: Aschbacher--Smith, 15.1.11, printed p.1089, using E.2.15 and D.1.2.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The strict outside-core bound on the original whole local action. -/
theorem source_outsideCore_full_cubicRatio_lt_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) < 2 := by
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  let := d.module_elementary
  let V := localModule T M
  let N := M
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := (d.module_le_core.trans (left_core_le_sylow d)).trans hH.1.1.2
  obtain ⟨hE,hTV,hq⟩ := source_outsideCore_sylow_cubicRatio hG T hM hJ H hH hout
  let := hE
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let σ := imageRepresentation N V (le_normalizer_conjugateSpanBy _ _)
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* N :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict N (fun s => hM.1.2 s.property)
  let f := (actionHom N V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict.comp i
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
  exact (cubicRatio_le_of_injective_equivariant ρ σ ψ hψi E he).trans_lt hq

/-- The ratio-two branch of original 15.1.11: the original local module lies
in every outside local two-core, and every such conjugate span is elementary. -/
theorem source_inside_all_cores_of_two_le_cubicRatio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    2 ≤ cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M →
      localModule T M ≤ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro hq H hH
  have hcore : localModule T M ≤ H.pCoreIn 2 := by
    by_contra hout
    exact (not_lt_of_ge hq)
      (source_outsideCore_full_cubicRatio_lt_two hG T hM hH hJ hout)
  refine ⟨hcore,?_⟩
  let V := localModule T M
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  have hnf : ¬IsFFModule ρ := by
    intro hf
    have hh := hq.trans ((cubicRatio_le_quadraticRatio ρ).trans
      ((isFFModule_iff_quadraticRatio_le_one ρ).mp hf))
    norm_num at hh
  apply conjugateSpan_elementary_of_notFF M H V f.rangeRestrict ρ
    (by rw [MonoidHom.ker_rangeRestrict]; exact actionHom_ker _ _ _) (fun _ _ => rfl) ?_ hnf
  intro g hg
  have hc : (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H hg)
  have ht : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  exact ((map_mono hcore).trans_eq hc).trans (ht.trans hM.1.2)

end CFSG.Quasithin.Chapter15.Section01

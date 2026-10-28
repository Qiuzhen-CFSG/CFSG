module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalReduction
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.NormalSource
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
/-!
# The normalized-module numerical case of the source qrc theorem

If H∩M normalizes the original qrc module V, an outside-core V gives a
strict cubic bound on its literal Sylow centralizer quotient by the proved
normal-module E.2 source theorem. The same actor embeds into the original
M₀ conjugation image. The inside-core numerical reduction then leaves
only the genuine dual-FF alternative. No solvability or TI assumption is
added: normalization supplies the TI condition used internally by E.2.

This proves the E.2.13 input in case (II) of Aschbacher--Smith 3.1.6,
printed pp.573--574. The full-module application is 3.2.5--6, pp.580--581.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.outsideCore_cubicRatio_le_two_of_intersection_normalizes
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hBV : H ⊓ M ≤ normalizer (V : Set G)) (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := h.module_elementary
  let σ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule σ
  · exact ((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans (by norm_num)
  have hVT : V ≤ (T : Subgroup G) := d.module_le_core.trans (left_core_le_sylow d)
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    by_contra hj
    exact hff (internalActionImage_isFFModule_of_thompson_not_le T M₀ V h.sylow_le
      hVT h.module_normalized hj)
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := hVT.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let hp := h.intrinsic_minimalParabolic hM hu hJ
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => hVT hx
  have hBN : ChapterB.minimalParabolicMax S hp ≤ normalizer (W : Set H) := by
    rw [h.intrinsic_maximal_eq_intersection hp,←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => hBV hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) :=
    (ChapterB.minimalParabolicMax_spec S hp).2.trans hBN
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W)
      (hWS.trans (ChapterB.minimalParabolicMax_spec S hp).2) hBN
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  have hbound := ChapterE.Witnesses.source_normal_cubicRatio_lt_two
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp W S hWS hWcore hWout hBN hfit le_rfl hTV
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* M₀ :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict M₀ (fun s => h.sylow_le s.property)
  let f := (actionHom M₀ V h.module_normalized).rangeRestrict.comp i
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
    exact (he a v).trans ((congrArg (fun z => σ z (E v)) hab).trans (he b v).symm)
  exact cubicRatio_le_nat_of_equivariant ρ σ ψ hψi E he 2 hbound.le

theorem QrcHypotheses.cubicRatio_le_two_or_dualFF_of_intersection_normalizes
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) (hBV : H ⊓ M ≤ normalizer (V : Set G)) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      DualFF (h.toQRCConfiguration (h.no_common_normal hu)) := by
  let := h.module_elementary
  rcases h.cubicRatio_le_two_or_source_branch hG hM hu hne with hq | ho | hd
  · exact Or.inl hq
  · exact Or.inl (h.outsideCore_cubicRatio_le_two_of_intersection_normalizes hG hM hu hBV ho)
  · exact Or.inr hd
end CFSG.Quasithin.Chapter3

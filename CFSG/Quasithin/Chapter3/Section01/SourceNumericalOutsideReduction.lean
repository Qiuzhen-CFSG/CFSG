module
public import CFSG.Quasithin.Chapter3.Section01.SourceE213CoreInput
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.NoTISourceReduction
/-!
# The no-TI outside-core numerical reduction on the original qrc action

The qrc and characteristic-two hypotheses supply every input of E.2.8 on
the literal intrinsic H, including V ≤ O₂(H ∩ M). The no-TI source witness
construction yields the cubic bound except for odd PSL3 and nonbinary Sp4.
The bound is transported through the Sylow centralizer quotient into the
original M₀ conjugation image; the exceptional alternatives retain their
actual normal component and full maximal-core quotient.

Source: Aschbacher--Smith 3.1.6(i), printed pp.573--574, using E.2.13(3),
printed pp.224--225. The two displayed model cases still require their source
module geometry; this theorem does not assert the missing numerical bounds.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The exact remaining source model rows of E.2.13, on the original H quotient. -/
@[expose] def QrcHypotheses.HasExceptionalOutsideCoreModel
    (h : QrcHypotheses T M M₀ H V) : Prop :=
  ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤,
  ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
    K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤ ∧
    ((∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.right_mem.1.1.2) hp))) 3 p) ∨
     (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.right_mem.1.1.2) hp))) 2 (2^f)))

theorem QrcHypotheses.outsideCore_cubicRatio_le_two_or_exceptional_model
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      h.HasExceptionalOutsideCoreModel := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := h.module_elementary
  let σ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule σ
  · exact Or.inl (((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans (by norm_num))
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
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => h.module_normalized (h.sylow_le hx)
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
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
  rcases ChapterE.Witnesses.source_cubicRatio_le_two_or_oddLinearThree_or_nonbinary_symplectic
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp W S hWS hvn hWcore hWout hfit le_rfl hTV with
      hbound | hm
  · apply Or.inl
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
    exact cubicRatio_le_nat_of_equivariant ρ σ ψ hψi E he 2 hbound

  · exact Or.inr ⟨hp,hm⟩

end CFSG.Quasithin.Chapter3

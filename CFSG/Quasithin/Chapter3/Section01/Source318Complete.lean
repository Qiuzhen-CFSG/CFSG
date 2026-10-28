module
public import CFSG.Quasithin.Chapter3.Section01.Source318Guarded
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.ResidualSylow
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.ActionQuotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# The guarded source Theorem 3.1.8(1)

Embed the original reduced subgroup of L∨T into G and construct the
literal qrc hypotheses. The two-residual remains L, so normality in M
supplies case (I). The genuine common-normal theorem and uniqueness
exclude a zero module. The proved qrc bound then transfers from the
conjugation image to the original quotient by its centralizer, with the
same reduced subgroup and action. An actual outside maximal two-local
supplies the HStar witness required by the source standing assumption.

Source: Aschbacher--Smith, Theorem 3.1.8(1), printed p.576, using the
standing assumption following Theorem 2.1.1 and Hypothesis 3.1.5.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The original reduced subgroup and Sylow centralizer identity supply
Hypothesis 3.1.5, with its residual-normalizer case (I). -/
theorem qrcHypotheses_of_reduced_join
    (T : Sylow 2 G) (M L H : Subgroup G)
    (hL : IsPPerfect 2 L) (hLM : L ≤ M) (hLN : (L.subgroupOf M).Normal)
    (hLTM : L ⊔ (T : Subgroup G) ≤ M) (hH : H ∈ HStar (T : Subgroup G) M)
    (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) (hV : IsPReduced 2 V)
    (hc : (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    QrcHypotheses T M (L ⊔ (T : Subgroup G)) H
      (V.map (L ⊔ (T : Subgroup G)).subtype) := by
  let M₀ := L ⊔ (T : Subgroup G)
  let W := V.map M₀.subtype
  let := hV.normal
  let := hV.elementary
  have hWV : W.subgroupOf M₀ = V :=
    comap_map_eq_self_of_injective M₀.subtype_injective V
  have hn : M₀ ≤ normalizer (W : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using V.le_normalizer_map M₀.subtype
  have hr : IsPReduced 2 (W.subgroupOf M₀) := hWV.symm ▸ hV
  refine ⟨le_sup_right, hLTM, hH, map_subtype_le V, hn,
    IsElementaryAbelian.map M₀.subtype, ?_, ?_, Or.inl ?_⟩
  · exact Section02.internalActionImage_core_of_reduced M₀ W
      (map_subtype_le V) hn hr
  · have he := congrArg (map M₀.subtype) hc
    rw [map_inf _ _ _ M₀.subtype_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M₀ from le_sup_right),
      map_centralizer_subtype, ← inf_assoc,
      inf_eq_left.mpr (show (T : Subgroup G) ≤ M₀ from le_sup_right)] at he
    exact he.symm
  · have hML : M ≤ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hLM).mp hLN
    rw [embedded_pResidual_join_pGroup L (T : Subgroup G) hL T.isPGroup'
      ((le_sup_right.trans hLTM).trans hML)]
    exact inf_le_right.trans hML

/-- Uniqueness and the genuine common-normal theorem exclude a zero module:
its core would be the whole ambient Sylow subgroup. -/
theorem QrcHypotheses.module_ne_bot_of_source_uniqueness
    {T : Sylow 2 G} {M M₀ H W : Subgroup G}
    (h : QrcHypotheses T M M₀ H W)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M) : W ≠ ⊥ := by
  intro he
  have hR : M₀.pCoreIn 2 = (T : Subgroup G) := by
    rw [h.core_eq_centralizer, he]
    apply inf_eq_left.mpr
    intro x hx y hy
    have hy' : y = 1 := mem_bot.mp hy
    simp only [hy', one_mul, mul_one]
  have hHT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hs := pCoreIn_le_sylow H (T.subtype h.right_mem.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hs
    rwa [map_subgroupOf_eq_of_le h.right_mem.1.1.2] at hs
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    exact h.right_mem.1.1.1 (eq_bot_iff.mpr (ht ▸ hHT))
  have hnot := h.not_residual_sylow (source_common_normal_knownSimple hG T)
    (hR.symm ▸ hTne) hu
  apply hnot
  rw [hR]
  exact ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩

/-- The cubic bound on the literal original reduced subgroup and its
centralizer quotient, from an actual HStar witness. -/
theorem source_reduced_join_cubicRatio_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (M L H : Subgroup G)
    (hL : IsPPerfect 2 L) (hLM : L ≤ M) (hLN : (L.subgroupOf M).Normal)
    (hM : IsMaximalTwoLocal M) (hLTM : L ⊔ (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hH : H ∈ HStar (T : Subgroup G) M)
    (V : Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) (hV : IsPReduced 2 V)
    (hc : (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    letI := hV.normal
    letI := hV.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (L ⊔ (T : Subgroup G) : Subgroup G))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let M₀ := L ⊔ (T : Subgroup G)
  let W := V.map M₀.subtype
  let := hV.normal
  let := hV.elementary
  have hWV : W.subgroupOf M₀ = V :=
    comap_map_eq_self_of_injective M₀.subtype_injective V
  have hq := qrcHypotheses_of_reduced_join T M L H hL hLM hLN hLTM hH V hV hc
  let := hq.module_elementary
  have hb := hq.source_cubicRatio_le_two hG hM hu
    (hq.module_ne_bot_of_source_uniqueness hG hu)
  let q := QuotientGroup.mk' (centralizer (V : Set M₀))
  have hk : q.ker = centralizer (W.subgroupOf M₀ : Set M₀) := by
    rw [hWV]
    exact QuotientGroup.ker_mk' _
  have ht := ChapterD.UniqueFactor.cubicRatio_quotient_le_nat_of_image M₀ W
    hq.module_le hq.module_normalized q (QuotientGroup.mk'_surjective _) hk 2 hb
  have htrans (U : Subgroup M₀) (he : U = V)
      (hUn : U.Normal) (hUe : IsElementaryAbelian 2 U)
      (hUk : q.ker = centralizer (U : Set M₀)) :
      letI := hUn
      letI := hUe
      cubicRatio (Representation.NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) hUk) ≤ 2 →
      cubicRatio (Representation.NormalElementaryQuotient.representation V q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
    subst U
    exact id
  exact htrans (W.subgroupOf M₀) hWV
    (normal_subgroupOf_of_le_normalizer hq.module_normalized)
    (IsElementaryAbelian.subgroupOf hq.module_le) hk ht

/-- The fixed-local 3.1.8 implication under the source standing guard. -/
theorem source_theorem318OneAt
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {M : Subgroup G} (hout : HasMaximalOutside T M) :
    SourceTheorem318OneAt T M := by
  obtain ⟨H, hH⟩ := exists_HStar_of_hasMaximalOutside hout
  apply SourceTheorem318OneAt.of_cubicRatio_le
  intro L hL hLM hLN hM hLTM hu V hV hc
  exact source_reduced_join_cubicRatio_le_two hG T M L H hL hLM hLN hM hLTM hu hH V hV hc

/-- The complete guarded source Theorem 3.1.8(1), proved from simple QTKE. -/
theorem source_guardedTheorem318One
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    GuardedSourceTheorem318One G :=
  GuardedSourceTheorem318One.of_fixedLocal
    (fun _ _ _ _ hout => source_theorem318OneAt hG hout)

end CFSG.Quasithin.Chapter3

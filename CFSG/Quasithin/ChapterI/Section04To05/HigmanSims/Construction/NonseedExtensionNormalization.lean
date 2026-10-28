module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.TwoNonseedExtensions
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEightNormalizerAction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import Theory.SpecificGroups.SymmetricFourSmallQuotient

/-!
# The original point core normalizes both elementary-sixteen extensions

The normalizer of the nonseed eight permutes its two actual extensions.
Its full centralizer fixes either extension, since the extension has index
two there. The induced stabilizer therefore has index at most two in the
full S4 action on the eight, and contains its normal Klein four. This is
the actual image of the original point core, so that core fixes both
literal extensions supplied by the source construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem core_normalizes_extension (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) (A B : Subgroup G)
    (hEA : E.val ≤ A) (hAe : IsElementaryAbelian 2 A) (hA16 : Nat.card A = 16)
    (hne : A ≠ B)
    (hall : ∀ F : Subgroup G, E.val ≤ F → IsElementaryAbelian 2 F →
      Nat.card F = 16 → F = A ∨ F = B) :
    (involutionCentralizer z).pCoreIn 2 ≤ normalizer (A : Set G) := by
  classical
  let H := involutionCentralizer z
  let N := H ⊓ normalizer (E.val : Set G)
  let K := centralizer (E.val : Set G)
  let Q := H.pCoreIn 2
  let L := (normalizer (A : Set G)).subgroupOf N
  let S := MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val)
  let f := pointCoreEightPointAction E
  let : IsElementaryAbelian 2 A := hAe
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hAK : A ≤ K := by
    intro a ha e he
    exact setLike_mul_comm (hEA he) ha
  have hKN : K ≤ N := by
    refine le_inf ?_ (centralizer_le_normalizer _)
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hk z E.property.2.1).symm
  have hKA : K ≤ normalizer (A : Set G) := by
    have hi : (A.subgroupOf K).index = 2 := by
      have hh := (A.subgroupOf K).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, hA16,
        h.point_core_nonseed_eight_centralizer_card E hEn] at hh
      omega
    let : (A.subgroupOf K).Normal := (A.subgroupOf K).normal_of_index_eq_two hi
    exact (normal_subgroupOf_iff_le_normalizer hAK).mp inferInstance
  have hk : f.ker = K.subgroupOf N := by
    ext g
    change pointCoreEightPointAction E g = 1 ↔ (g : G) ∈ K
    rw [Subtype.ext_iff]
    change E.val.normalizerMonoidHom (inclusion inf_le_right g) = 1 ↔ (g : G) ∈ K
    change inclusion inf_le_right g ∈ E.val.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hker : f.ker ≤ L := by
    rw [hk]
    exact fun g hg => hKA hg
  let : MulAction N (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp N.subtype)
  have hL : MulAction.stabilizer N A = L := by
    ext g
    change A.map (MulAut.conj (g : G)).toMonoidHom = A ↔
      (g : G) ∈ normalizer (A : Set G)
    exact mem_normalizer_iff_map_conj_eq.symm
  have hiL : L.index ≤ 2 := by
    rw [← hL, MulAction.index_stabilizer]
    have hsub : MulAction.orbit N A ⊆ {A, B} := by
      rintro F ⟨g, rfl⟩
      have he : E.val.map (MulAut.conj (g : G)).toMonoidHom = E.val :=
        mem_normalizer_iff_map_conj_eq.mp g.property.2
      have hEF : E.val ≤ g • A := by
        change E.val ≤ A.map (MulAut.conj (g : G)).toMonoidHom
        rw [← he]
        exact map_mono hEA
      have hFe : IsElementaryAbelian 2 (g • A : Subgroup G) :=
        IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
      have hFc : Nat.card (g • A : Subgroup G) = 16 :=
        (card_map_of_injective (MulAut.conj (g : G)).injective).trans hA16
      exact hall (g • A) hEF hFe hFc
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hne)
  have hf : Function.Surjective f := h.point_core_nonseed_eight_point_action_surjective E hEn
  have hS24 : Nat.card S = 24 := by
    have hh := f.ker.card_mul_index
    rw [index_ker, f.range_eq_top_of_surjective hf, card_top, hk,
      Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv,
      h.point_core_nonseed_eight_centralizer_card E hEn,
      h.point_core_nonseed_eight_normalizer_card E hEn] at hh
    change 32 * Nat.card S = 768 at hh
    omega
  have hz : (⟨z, E.property.2.1⟩ : E.val) ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have hi := h.involution
    simp [hz1] at hi
  obtain ⟨e⟩ := elementaryEight_fixed_point_order24_equiv_S4 E.property.2.2.2
    ⟨z, E.property.2.1⟩ hz S hS24 (fun a => a.property)
  let J := L.map f
  have hiJ : J.index ≤ 2 := by
    rw [L.index_map_eq hf hker]
    exact hiL
  let : J.Normal := by
    by_cases hj : J.index = 1
    · rw [index_eq_one.mp hj]
      infer_instance
    · have hp := J.index_ne_zero_of_finite
      exact J.normal_of_index_eq_two (by omega)
  have hcore : pCore 2 S ≤ J := by
    have hh := Theory.SpecificGroups.SymmetricFour.twoCore_le_ker_of_equiv_of_card_lt
      e (QuotientGroup.mk' J) (by change J.index < 24; omega)
    simpa only [QuotientGroup.ker_mk'] using hh
  have hQN : Q ≤ N := by
    refine le_inf (pCoreIn_le 2 H) ?_
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro q hq a ha
    exact (zpowers_le.mpr E.property.2.1)
      (h.point_core_commutator_mem q a hq (E.property.1 ha))
  intro q hq
  let qN : N := ⟨q, hQN hq⟩
  have hqf : f qN ∈ pCore 2 S := by
    rw [← h.point_core_nonseed_eight_core_image E hEn]
    exact mem_map_of_mem f (show qN ∈ Q.subgroupOf N from hq)
  have hqL : qN ∈ (L.map f).comap f := hcore hqf
  rw [comap_map_eq, sup_eq_left.mpr hker] at hqL
  exact hqL

/-- Original HS data give the two literal extensions and an original point
core normalizing each of them, retaining the same central cyclic-four
generator and the same seed-class involution from the construction. -/
theorem TypeAt.exists_core_normalized_nonseed_eight_extensions (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧ E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ ∧
      (center (centralizer (E.val : Set G))).map
        (centralizer (E.val : Set G)).subtype = E.val ∧
      let A := E.val ⊔ zpowers b
      let B := E.val ⊔ zpowers (c * b)
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E.val ∧
      (involutionCentralizer u).pCoreIn 2 ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768,
    hc4, hc2, hcZ, hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hall⟩ :=
    h.exists_two_nonseed_eight_extensions
  have hQA := core_normalizes_extension huT E hEn _ _ le_sup_left hAe hA16 hne
    (fun F hEF hFe hF16 => (hall F).mp ⟨hEF, hFe, hF16⟩)
  have hQB := core_normalizes_extension huT E hEn _ _ le_sup_left hBe hB16 hne.symm
    (fun F hEF hFe hF16 => ((hall F).mp ⟨hEF, hFe, hF16⟩).symm)
  exact ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768,
    hc4, hc2, hcZ, hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi,
    le_inf hQA hQB, hall⟩

end CFSG.Quasithin.HigmanSims

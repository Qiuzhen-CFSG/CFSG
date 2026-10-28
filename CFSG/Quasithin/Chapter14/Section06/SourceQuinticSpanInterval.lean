module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanOrder
public import Theory.GroupAction.FaithfulSixteen

/-!
# Irreducibility of the original quintic center layer

The actual center layer UH/ZT has order sixteen and a faithful Sz(2)
action. Its original H-invariant interval is therefore trivial. Applied
to the intersection with the full derived core, this leaves exactly the
central-line branch or containment of the whole UH in the derived core.
The central-line branch still needs geometric exclusion; no equality of
the full kernel C with UH is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The genuine center-layer action gives the original invariant interval
and the resulting precise derived-core alternative. -/
theorem source_quintic_span_interval_and_derived
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Z := centralInvolutions T
    let Q := H.pCoreIn 2
    (∀ D : Subgroup G, Z ≤ D → D ≤ U → H ≤ normalizer (D : Set G) →
      D = Z ∨ D = U) ∧
      (U ⊓ ⁅Q,Q⁆ = Z ∨ U ≤ ⁅Q,Q⁆) := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let Q := H.pCoreIn 2
  obtain ⟨hN,α,hker,hnot,hα⟩ := source_quintic_faithful_center_layer_action
    hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let W := U ⧸ Z.subgroupOf U
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZ : Nat.card (Z.subgroupOf U) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv).trans
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hU : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hW : Nat.card W = 16 := by
    have hh := (Z.subgroupOf U).card_mul_index
    change Nat.card (Z.subgroupOf U) * Nat.card W = Nat.card U at hh
    rw [hZ,hU] at hh
    omega
  have h5 : 5 ∣ Nat.card α.range := by
    have hh : Nat.card α.range = Nat.card (H ⧸ pCore 2 H) := by
      rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv,hker]
    obtain ⟨eS⟩ := (source_quintic_suzuki_zero_quotient
      hG T hempty hM hu hmany hcard e H hH hi).2
    rw [hh,(Nat.card_congr eS.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]
    decide
  have hinterval (D : Subgroup G) (hZD : Z ≤ D) (hDU : D ≤ U)
      (hnD : H ≤ normalizer (D : Set G)) : D = Z ∨ D = U := by
    let π := QuotientGroup.mk' (Z.subgroupOf U)
    let R := (D.subgroupOf U).map π
    have hforward (h : H) (w : W) (hw : w ∈ R) : α h w ∈ R := by
      obtain ⟨u,hu',rfl⟩ := hw
      rw [hα]
      apply mem_map_of_mem π
      exact (mem_normalizer_iff.mp (hnD h.property) u).mp hu'
    have hinv (h : H) (w : W) : w ∈ R ↔ α h w ∈ R := by
      refine ⟨hforward h w,?_⟩
      intro hw
      have hh := hforward h⁻¹ (α h w) hw
      simpa only [map_inv,MulAut.inv_apply,MulEquiv.symm_apply_apply] using hh
    rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five α h5 hW R hinv with he | he
    · left
      apply le_antisymm ?_ hZD
      have hh : D.subgroupOf U ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp he
      rw [QuotientGroup.ker_mk'] at hh
      intro d hd
      exact hh (show (⟨d,hDU hd⟩ : U) ∈ D.subgroupOf U from hd)
    · right
      apply le_antisymm hDU
      have he' : (D.subgroupOf U).map π = ⊤ := he
      have hm : (⊤ : Subgroup U).map π ≤ (D.subgroupOf U).map π := by rw [he']; exact le_top
      have hh := map_le_map_iff.mp hm
      rw [QuotientGroup.ker_mk',sup_of_le_left (subgroupOf_mono U hZD)] at hh
      intro u hu'
      exact hh (mem_top (⟨u,hu'⟩ : U))
  refine ⟨hinterval,?_⟩
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hZder : Z ≤ ⁅Q,Q⁆ := by
    have hh := (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
    change ⁅U,Q⁆ = Z at hh
    exact hh.ge.trans (commutator_mono hUQ le_rfl)
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHder : H ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHQ hh)]
  have hHI : H ≤ normalizer ((U ⊓ ⁅Q,Q⁆ : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_conjugateSpanBy _ _) hHder).trans inf_normalizer_le_normalizer_inf
  rcases hinterval (U ⊓ ⁅Q,Q⁆) (le_inf hZU hZder) inf_le_left hHI with he | he
  · exact Or.inl he
  · exact Or.inr (he.ge.trans inf_le_right)

end CFSG.Quasithin.Chapter14.Section06

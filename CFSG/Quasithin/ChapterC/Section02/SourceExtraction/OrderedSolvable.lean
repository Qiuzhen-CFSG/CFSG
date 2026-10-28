module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Solvable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Product

/-!
# Ordered solvable A₃-block products outside characteristic control

The genuine solvable minimal-parabolic theorem supplies a moved A₃-block
outside every proper characteristic-normalizer overgroup. Take all such
blocks outside the specified subgroup M. Sylow conjugation preserves this
family, its join is normal, and distinct blocks commute. The outside-block
theorem makes their join supplement M. The three-rank bound permits at most
two factors, yielding an ordered product of the original outside A₃-blocks.

This is the solvable local C(G,T) theorem used in C.2.6. No product, block
selection, or nonsolvable C.1.28 implication is assumed.
Source: Aschbacher–Smith C.1.26–29 and C.2.6, printed pp.132–145.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section02Source
universe u
variable {G : Type u} [Group G] [Finite G]

theorem exists_outside_moved_a3
    (h : SectionTwo.Hypotheses G) (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M < ⊤) :
    ∃ K : Subgroup G, ¬ K ≤ M ∧ (IsBlock K ∧ IsAlternatingBlock K 3) ∧
      K = ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  obtain ⟨H, hH, hout⟩ := RankOne.Solvable.exists_minimalParabolic_not_le h T M hcpu hM
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.le
  have hh := RankOne.Solvable.sectionTwoHypotheses_of_sylow_le h T H hTH
  have hP := RankOne.Solvable.characteristic_obstruction_of_not_le T H M hTH hcpu hout
  have hu := RankOne.Solvable.uniqueMaximalContaining_of_minimalParabolic T H hH
  have hMH : M.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hout (subgroupOf_eq_top.mp he))
  have hTM : (T : Subgroup G) ≤ M := by
    have hTne := T.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
    exact (T : Subgroup G).le_normalizer.trans ((normalizer_le_characteristicNormalizerClosure_self
      (T : Subgroup G) hTne).trans hcpu)
  obtain ⟨K₀, hKout, hb, ha, hJ, hU⟩ := RankOne.Solvable.exists_outside_alternatingThree_block
    hh (T.subtype hTH) hP hu (M.subgroupOf H) (comap_mono hTM) hMH
  let K := K₀.map H.subtype
  let e : K₀ ≃* K := equivMapOfInjective K₀ H.subtype H.subtype_injective
  have hKH : K ≤ H := map_subtype_le _
  have hsub : (K.subgroupOf H).IsSubnormal := by
    simpa only [K, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using
      hb.subnormal
  have haK : IsAlternatingBlock K 3 := RankOne.Solvable.isAlternatingBlock_of_equiv e ha
  have hJK : K = ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hm := congrArg (Subgroup.map H.subtype) hJ
    rw [map_commutator, ← elementaryAbelianMaxJ_map_injective
      H.subtype H.subtype_injective, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] at hm
    exact hm
  have hUK : (blockU K).map K.subtype ≤
      (SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype := by
    rw [← RankOne.Solvable.blockU_map_equiv e, map_map]
    have hm := Subgroup.map_mono (f := H.subtype) hU
    rw [map_map] at hm
    exact hm
  refine ⟨K, ?_, ⟨⟨inferInstance, haK.2.1,
    RankOne.Solvable.isSubnormal_of_local_alternatingThree h T hTH hKH hsub haK hJK hUK⟩,
    haK⟩, hJK⟩
  intro hKM
  exact hKout (map_le_iff_le_comap.mp hKM)


theorem ordered_alternatingThree_product
    (hs : Group.IsSolvable G)
    {κ : GroupClass} (hG : IsSQTK κ G) (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsBlock (L i) ∧ IsAlternatingBlock (L i) 3) ∧ (∀ i, ¬L i ≤ M) ∧
      (∀ i, L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆) ∧
      ∀ g : G, ∃ m : M, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod := by
  classical
  have hTM : (T : Subgroup G) ≤ M := by
    by_cases ht : (T : Subgroup G) = ⊥
    · rw [ht]; exact bot_le
    · exact (T : Subgroup G).le_normalizer.trans
        ((normalizer_le_characteristicNormalizerClosure_self _ ht).trans hcpu)
  have hr : primeRank 3 G ≤ 2 := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  let I := {L : Subgroup G // (IsBlock L ∧ IsAlternatingBlock L 3) ∧
    L = ⁅L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧ ¬L ≤ M}
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let L : Fin r → Subgroup G := fun i => (e.symm i).val
  have hLa (i) : IsBlock (L i) ∧ IsAlternatingBlock (L i) 3 := (e.symm i).property.1
  have hL (i) : IsChiBlockIn (L i) := ⟨(hLa i).1, Or.inr ⟨3, by decide, (hLa i).2⟩⟩
  have hm (i) : L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
    (e.symm i).property.2.1
  have hout (i) : ¬L i ≤ M := (e.symm i).property.2.2
  have hi : Function.Injective L := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hguard := RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf
  have hr' : r ≤ 2 := by
    have hh := (RankOne.ChiProduct.card_le_threeRank hguard L hi hL).trans hr
    simpa only [Fintype.card_fin] using hh
  let X := ⨆ i, L i
  have hmem {B : Subgroup G} (hB : IsBlock B ∧ IsAlternatingBlock B 3)
      (hb : B = ⁅B, elementaryAbelianMaxJ (T : Subgroup G)⁆) (hn : ¬B ≤ M) : B ≤ X := by
    let b : I := ⟨B, hB, hb, hn⟩
    have he : L (e b) = B := by dsimp [L]; rw [e.symm_apply_apply]
    exact he ▸ le_iSup L (e b)
  let Y : Fin r → Subgroup G := fun i => conjugateSpanBy (L i) (T : Subgroup G)
  let (i : Fin r) : (Y i).Normal := conjugateSpanBy_sylow_normal (L i) T
    (RankOne.ChiProduct.normal_or_index_two hf hr (hL i))
  have hXY : X = ⨆ i, Y i := by
    apply le_antisymm
    · exact iSup_le fun i => (le_conjugateSpanBy (L i) _).trans (le_iSup Y i)
    · apply iSup_le
      intro i
      change conjugateSpanBy (L i) (T : Subgroup G) ≤ X
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro t
      apply hmem ⟨(RankOne.ChiProduct.chi_map_equiv (MulAut.conj (t : G)) (hL i)).1,
        RankOne.Solvable.isAlternatingBlock_of_equiv
          (equivMapOfInjective (L i) (MulAut.conj (t : G)).toMonoidHom (MulAut.conj (t : G)).injective) (hLa i).2⟩
        (RankOne.ChiProduct.moved_conjugate _ (hm i) t)
      intro hle
      apply hout i
      intro x hx
      have hxM := hle (mem_map_of_mem (MulAut.conj (t : G)).toMonoidHom hx)
      have htM := hTM t.property
      have hh := M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
      change (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * (t : G) ∈ M at hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  let : X.Normal := by rw [hXY]; infer_instance
  have hgen : M ⊔ X = ⊤ := by
    by_contra hn
    have hsection := RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup hs
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) (M ⊔ X) (lt_top_iff_ne_top.mpr hn)
    obtain ⟨B, hb, hB, hmB⟩ := exists_outside_moved_a3
      hsection T (M ⊔ X) (hcpu.trans le_sup_left) (lt_top_iff_ne_top.mpr hn)
    exact hb ((hmem hB hmB (fun hh => hb (hh.trans le_sup_left))).trans le_sup_right)
  have hc : Pairwise fun i j => L i ≤ centralizer (L j : Set G) :=
    fun i j hij => commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute hguard (hL i).1 (hL j).1 (fun he => hij (hi he)))
  refine ⟨r, hr', L, hLa, hout, hm, fun g => ?_⟩
  obtain ⟨m, hmM, x, hx, he⟩ := mem_sup_of_normal_right.mp
    (show g ∈ M ⊔ X by rw [hgen]; exact mem_top g)
  obtain ⟨b, hb⟩ := RankOne.ChiProduct.ordered_product_of_mem_iSup L hc hx
  exact ⟨⟨m, hmM⟩, b, he.symm.trans (congrArg (fun x => m * x) hb)⟩
end CFSG.Quasithin.ChapterC.Section02Source

module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Product
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source

/-!
# The complete solvable χ-product source

The existing minimal-parabolic construction gives an actual A₃-block
outside characteristic-normalizer control, its original Thompson movement,
and its support inside the local omega-center module. The ambient extension
retains that same subgroup. Keeping the movement identity gives the
outside-block input to the normal-layer product theorem.

Thus the ordered product with at most two moved χ-blocks is proved from
the original solvable characteristic-two SQTK hypotheses. No selected block,
action quotient, characteristic pair or product is an input.

Source: Aschbacher–Smith C.1.26–29, printed pp.132–134; the solvable
minimal-parabolic calculation is Stellmacher, Section Two.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

/-- The specified local A₃-block extends unchanged and has a normal Sylow
orbit. Characteristic-normalizer control is not needed for this propagation. -/
theorem local_alternatingThree_normal_span
    (h : SectionTwo.Hypotheses G) (hr : primeRank 3 G ≤ 2) (T : Sylow 2 G)
    {H K : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (ha : IsAlternatingBlock K 3)
    (hJ : K = ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hU : (blockU K).map K.subtype ≤
      (SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype) :
    IsChiZeroBlockIn K ∧ (conjugateSpanBy K (T : Subgroup G)).Normal ∧
      conjugateSpanBy K (T : Subgroup G) =
        ⁅conjugateSpanBy K (T : Subgroup G), elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hK : IsChiZeroBlockIn K :=
    ⟨⟨inferInstance, ha.2.1,
      Solvable.isSubnormal_of_local_alternatingThree h T hTH hKH hsub ha hJ hU⟩,
      Or.inr (Or.inl ha)⟩
  have hf : generalizedFitting G = pCore 2 G :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr h.centralizer_twoCore_le
  refine ⟨hK, conjugateSpanBy_sylow_normal K T
    (normal_or_index_two hf hr hK.chi), ?_⟩
  exact (commutator_conjugateSpanBy_eq_self K (T : Subgroup G)
    (elementaryAbelianMaxJ (T : Subgroup G))
    (sSup_le fun _ hA => hA.1)
    ((T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)) hJ.symm).symm

/-- Retain the original J(T)-movement in the existing solvable outside-block
construction. All subgroups and local-module maps are the actual inclusions. -/
theorem exists_outside_moved_alternatingThree
    (h : SectionTwo.Hypotheses G) (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M < ⊤) :
    ∃ K : Subgroup G, ¬ K ≤ M ∧ IsChiZeroBlockIn K ∧
      K = ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  obtain ⟨H, hH, hout⟩ := Solvable.exists_minimalParabolic_not_le h T M hcpu hM
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.le
  have hh := Solvable.sectionTwoHypotheses_of_sylow_le h T H hTH
  have hP := Solvable.characteristic_obstruction_of_not_le T H M hTH hcpu hout
  have hu := Solvable.uniqueMaximalContaining_of_minimalParabolic T H hH
  have hMH : M.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hout (subgroupOf_eq_top.mp he))
  have hTM : (T : Subgroup G) ≤ M := by
    have hTne := T.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
    exact (T : Subgroup G).le_normalizer.trans ((normalizer_le_characteristicNormalizerClosure_self
      (T : Subgroup G) hTne).trans hcpu)
  obtain ⟨K₀, hKout, hb, ha, hJ, hU⟩ := Solvable.exists_outside_alternatingThree_block
    hh (T.subtype hTH) hP hu (M.subgroupOf H) (comap_mono hTM) hMH
  let K := K₀.map H.subtype
  let e : K₀ ≃* K := equivMapOfInjective K₀ H.subtype H.subtype_injective
  have hKH : K ≤ H := map_subtype_le _
  have hsub : (K.subgroupOf H).IsSubnormal := by
    simpa only [K, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using
      hb.subnormal
  have haK : IsAlternatingBlock K 3 := Solvable.isAlternatingBlock_of_equiv e ha
  have hJK : K = ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hm := congrArg (Subgroup.map H.subtype) hJ
    rw [map_commutator, ← elementaryAbelianMaxJ_map_injective
      H.subtype H.subtype_injective, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH] at hm
    exact hm
  have hUK : (blockU K).map K.subtype ≤
      (SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype := by
    rw [← Solvable.blockU_map_equiv e, map_map]
    have hm := Subgroup.map_mono (f := H.subtype) hU
    rw [map_map] at hm
    exact hm
  refine ⟨K, ?_, ⟨⟨inferInstance, haK.2.1,
    Solvable.isSubnormal_of_local_alternatingThree h T hTH hKH hsub haK hJK hUK⟩,
    Or.inr (Or.inl haK)⟩, hJK⟩
  intro hKM
  exact hKout (map_le_iff_le_comap.mp hKM)

/-- C.1.28's literal ordered product in the solvable source case, uniformly
for every actual characteristic-normalizer overgroup. -/
theorem solvable_ordered_chi_product
    (hs : Group.IsSolvable G) (hqt : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsChiBlockIn (L i)) ∧
      (∀ i, L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆) ∧
      ∀ g : G, ∃ m : M, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod := by
  apply ordered_product_of_outside_moved hf
    (hqt.stronglyQuasithin 3 Nat.prime_three (by decide)) T M
  intro N hMN hN
  have hNlt : N < ⊤ := lt_top_iff_ne_top.mpr hN
  have hh := Solvable.sectionTwoHypotheses_of_proper_subgroup hs
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) N hNlt
  obtain ⟨L, hout, hL, hm⟩ := exists_outside_moved_alternatingThree
    hh T N (hcpu.trans hMN) hNlt
  exact ⟨L, hout, hL.chi, hm⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct

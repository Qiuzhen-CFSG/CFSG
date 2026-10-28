module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import CFSG.Quasithin.Chapter2.Section04.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
/-!
# Odd actors fix the original linear factors

The actual normalizer of O₂(H) normalizes the block product by 2.4.6.
Each short factor is therefore subnormal there. The genuine C.1 chi-product
orbit theorem bounds its orbit by two, so every odd subgroup fixes it.
This is the factor-stabilization input for the conjugate tori on printed
p.540 of Aschbacher--Smith, Section 2.4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normalizes_chiBlock
    (hG : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (L D : Subgroup G) (hL : ChapterC.IsChiBlockIn L)
    (ho : Odd (Nat.card D)) : D ≤ normalizer (L : Set G) := by
  rcases ChapterC.RankOne.ChiProduct.normal_or_index_two hG hr hL with hn | hi
  · rw [normalizer_eq_top_iff.mpr hn]
    exact le_top
  · let N := normalizer (L : Set G)
    let : N.Normal := normal_of_index_eq_two hi
    have hd : N.relIndex D ∣ 2 := hi ▸ relIndex_dvd_index_of_normal N D
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact relIndex_eq_one.mp he
    · exact (ho.not_two_dvd_nat (he ▸ relIndex_dvd_card N D)).elim

variable {M : Subgroup G}
/-- An odd subgroup of the original core normalizer fixes each linear factor. -/
theorem odd_coreNormalizer_normalizes_factor
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (L D : Subgroup G) (hLL : L ≤ d.L0.map d.H.subtype)
    (hLLN : d.L0.map d.H.subtype ≤ normalizer (L : Set G))
    (hLin : ChapterC.IsL2EvenBlock L n)
    (hDN : D ≤ normalizer (twoCore d.H : Set G)) (ho : Odd (Nat.card D)) :
    D ≤ normalizer (L : Set G) := by
  let N := normalizer (twoCore d.H : Set G)
  let L₀ := d.L0.map d.H.subtype
  have hL₀N : L₀ ≤ N := (map_subtype_le _).trans (le_normalizer_twoCore d.H)
  have hLN : L ≤ N := hLL.trans hL₀N
  have h3 : ¬ ChapterC.IsAlternatingBlock d.block 3 := by
    intro ha
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable d.block := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    have hs := hL.of_mulEquiv (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
    exact hs.not_solvable
  have hNN : N ≤ normalizer (L₀ : Set G) :=
    d.coreNormalizer_normalizes_L0_source_of_not_three hG T hM hTM hu h3
  let B := L₀.subgroupOf N
  let A := L.subgroupOf N
  have hBN : B.Normal := (normal_subgroupOf_iff_le_normalizer hL₀N).mpr hNN
  have hAB : A ≤ B := fun _ hx => hLL hx
  have hA₀ : (L.subgroupOf L₀).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLL).mpr hLLN
  let eB : B ≃* L₀ := subgroupOfEquivOfLe hL₀N
  have hAn : (A.subgroupOf B).Normal := by
    let := hA₀
    change ((L.subgroupOf L₀).comap eB.toMonoidHom).Normal
    infer_instance
  have hAs : A.IsSubnormal := IsSubnormal.trans hAB hAn.isSubnormal hBN.isSubnormal
  let eA : A ≃* L := subgroupOfEquivOfLe hLN
  have hA : ChapterC.IsL2EvenBlock A n := hLin.of_mulEquiv eA.symm
  have hc : ChapterC.IsChiBlockIn A := ⟨⟨inferInstance,hA.2.1,hAs⟩,.inl ⟨n,hA⟩⟩
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (hG.evenCharacteristic T M hM hTM)
  have hN := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hfit : generalizedFitting N = pCore 2 N :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hN.1.2)
  have hQne : twoCore d.H ≠ ⊥ := (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hr : primeRank 3 N ≤ 2 := (hG.twoLocal_sqtk
    (show IsTwoLocal N from ⟨twoCore d.H,hQne,isPGroup_pCoreIn 2 d.H,rfl⟩)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have ho' : Odd (Nat.card (D.subgroupOf N)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv]
  have hh := odd_normalizes_chiBlock hfit hr A (D.subgroupOf N) hc ho'
  intro z hz
  have hz' := hh (show (⟨z,hDN hz⟩ : N) ∈ D.subgroupOf N from hz)
  have hm := mem_normalizer_iff_map_conj_eq.mp hz'
  have he := congrArg (map N.subtype) hm
  rw [map_map] at he
  have hf : N.subtype.comp (MulAut.conj (⟨z,hDN hz⟩ : N)).toMonoidHom =
      (MulAut.conj z).toMonoidHom.comp N.subtype := rfl
  change map (N.subtype.comp (MulAut.conj (⟨z,hDN hz⟩ : N)).toMonoidHom) A = map N.subtype A at he
  rw [hf,←map_map,map_subgroupOf_eq_of_le hLN] at he
  exact mem_normalizer_iff_map_conj_eq.mpr he
/-- The literal paired setup needs no additional factor-stabilizer premise. -/
theorem odd_coreNormalizer_normalizes_pair
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (D : Subgroup G) (hDN : D ≤ normalizer (twoCore d.H : Set G))
    (ho : Odd (Nat.card D)) :
    D ≤ normalizer (d.block.map d.H.subtype : Set G) ⊓ normalizer (c.second : Set G) := by
  have hnorm₁ : d.L0.map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G) := by
    rw [←c.join]
    exact sup_le (d.block.map d.H.subtype).le_normalizer
      (c.commutes.trans (Subgroup.centralizer_le_normalizer _))
  have hnorm₂ : d.L0.map d.H.subtype ≤ normalizer (c.second : Set G) := by
    rw [←c.join]
    exact sup_le ((le_centralizer_iff.mp c.commutes).trans (Subgroup.centralizer_le_normalizer _))
      c.second.le_normalizer
  exact le_inf
    (odd_coreNormalizer_normalizes_factor d hG T hM hTM hu hL _ D
      (le_sup_left.trans_eq c.join) hnorm₁ hL hDN ho)
    (odd_coreNormalizer_normalizes_factor d hG T hM hTM hu hL _ D
      (le_sup_right.trans_eq c.join) hnorm₂ c.second_type hDN ho)
end CFSG.Quasithin.Chapter2.LinearDouble

module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvercomponentSource
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
/-!
# Center normalizers and TI for the original single block

Once all nonidentity central-element centralizers normalize the block,
the block is a C-component in its center normalizer. The original Sylow
normalizes it, so source component normality identifies both normalizers.
The actual transitive torus action gives TI, which forces every local
overgroup to normalize the block and yields the unique maximal overgroup.
The independent low-rank overcomponent contradiction supplies the sole
remaining centralizer input in the final assembly.

Source: Aschbacher–Smith, 2.4.11, printed p.532.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_center_normalizer_of_centralizers
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (hc : ∀ z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype,
      z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    normalizer ((center (d.block.map d.H.subtype)).map
      (d.block.map d.H.subtype).subtype : Set G) = normalizer (d.block.map d.H.subtype : Set G) := by
  let L := d.block.map d.H.subtype
  let Z := (center L).map L.subtype
  let N := normalizer (Z : Set G)
  let C := centralizer (Z : Set G)
  have hZn : Z ≠ ⊥ := (map_eq_bot_iff_of_injective _ L.subtype_injective).not.mpr hZ
  have hLN : L ≤ N := L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hLC : L ≤ C := by
    intro l hl z hz
    obtain ⟨a,ha,rfl⟩ := hz
    exact (congrArg Subtype.val (mem_center_iff.mp ha (⟨l,hl⟩ : L))).symm
  have hCL : C ≤ normalizer (L : Set G) := by
    obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hZn
    exact (centralizer_le (show ({(z:G)} : Set G) ⊆ Z from Set.singleton_subset_iff.mpr z.property)).trans
      (hc z z.property (fun he => hz (Subtype.ext he)))
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L : Set G) := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hHN : d.H ≤ N := hHL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hZQ : Z ≤ twoCore d.H := (map_mono (hK.center_le_module
    (source_block_core_eq_module d hG T hST hsingle))).trans_eq
      (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  have hN : N ∈ Chapter1.H G := Chapter1.mem_H_of_isTwoLocal
    ⟨Z,hZn,(isPGroup_pCoreIn 2 d.H).to_le hZQ,rfl⟩
  obtain ⟨_,⟨P,hP⟩,_⟩ := lemma_2_3_7_2 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl ⟨hN,hHN⟩
  have h3 : ¬ ChapterC.IsAlternatingBlock d.block 3 := by
    intro ha
    obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable d.block := Group.isSolvable_of_isSolvable_injective (f:=e.toMonoidHom) e.injective
    exact hL.not_solvable
  let B := L.subgroupOf N
  let C' := C.subgroupOf N
  let : C'.Normal := normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_centralizer Z)
  have hBC : B ≤ C' := comap_mono hLC
  have hCB : C' ≤ normalizer (B : Set N) := by
    apply le_normalizer_iff.mpr
    intro c hc b hb
    exact (mem_normalizer_iff.mp (hCL hc) (b:G)).mp hb
  have hBn : B.IsSubnormal := IsSubnormal.step _ _ hBC
    (inferInstance : C'.Normal).isSubnormal (normal_subgroupOf_of_le_normalizer hCB)
  have ht : (⊤ : Subgroup d.block).IsCComponent := by
    simpa only [subgroupOf_self] using (d.block_isCComponent_of_not_three h3).subgroupOf le_rfl
  let e : d.block ≃* B := (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective).trans
    (subgroupOfEquivOfLe hLN).symm
  have htB : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht.map_equiv e
  have hB : B.IsCComponent := by
    simpa only [←MonoidHom.range_eq_map,range_subtype] using htB.map_subtype hBn
  have hBL : B ∈ Chapter1.L N (P : Subgroup N) := by
    apply (Chapter1.mem_L_map_iff N.subtype N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hLN,hP]
    exact d.ambient_block_mem_L_of_not_three h3
  have hPN : (P : Subgroup N) ≤ normalizer (B : Set N) := by
    apply le_normalizer_iff.mpr
    intro p hp b hb
    have hpH : (p:G) ∈ d.H := map_subtype_le _ (hP ▸ mem_map_of_mem N.subtype hp)
    exact (mem_normalizer_iff.mp (hHL hpH) (b:G)).mp hb
  obtain ⟨K,⟨hcomp,hBK,hKn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hN) P hBL hPN
  have hnB : B.Normal := (hB.eq_of_le hcomp hBK).symm ▸ hKn
  exact le_antisymm ((normal_subgroupOf_iff_le_normalizer hLN).mp hnB)
    (normalizer_le_normalizer_characteristic_image L (center L))

theorem source_center_TI_of_centralizers
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (hc : ∀ z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype,
      z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    ChapterI.Section06To08.IsTISubgroup ((center (d.block.map d.H.subtype)).map
      (d.block.map d.H.subtype).subtype) := by
  let L := d.block.map d.H.subtype
  let Z := (center L).map L.subtype
  have hn := source_center_normalizer_of_centralizers d hG T hST hsingle hL hM hTM hunique hZ hc
  obtain ⟨_,D,_,_,_,x,_,_,hEL,hr⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  have hreg := (hr.resolve_left hZ).2.2
  apply ChapterI.Section06To08.lemma_I_6_1_1 Z (normalizer (L : Set G)) hn.symm hc
  intro z w hz hw hconj
  by_cases hz1 : z=1
  · obtain ⟨a,ha⟩ := hconj
    have hw1 : w=1 := by simpa only [hz1,mul_one,mul_inv_cancel] using ha.symm
    exact ⟨1,by simp only [OneMemClass.coe_one,inv_one,mul_one,hz1,hw1]⟩
  have hw1 : w≠1 := by
    intro he
    obtain ⟨a,ha⟩ := hconj
    have hh := congrArg (fun v:G => a⁻¹*v*a) (ha.trans he)
    exact hz1 (by simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_one,inv_mul_cancel] using hh)
  obtain ⟨a,ha,_⟩ := hreg ⟨z,hz⟩ (fun he => hz1 (congrArg Subtype.val he))
    ⟨w,hw⟩ (fun he => hw1 (congrArg Subtype.val he))
  exact ⟨⟨a,hEL a.property⟩,ha⟩

theorem source_overgroup_normalizes_of_centralizers
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hc : ∀ z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype,
      z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G))
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hLX : d.block.map d.H.subtype ≤ X) :
    X ≤ normalizer (d.block.map d.H.subtype : Set G) := by
  by_cases hZ : center (d.block.map d.H.subtype)=⊥
  · exact source_centerless_overgroup_normalizes d hG T hST hsingle hL hM hTM hunique hZ X hX hLX
  have ht := source_center_TI_of_centralizers d hG T hST hsingle hL hM hTM hunique hZ hc
  have hn := source_center_normalizer_of_centralizers d hG T hST hsingle hL hM hTM hunique hZ hc
  rcases source_overgroup_core_central_or_normalizes d hG T hST hsingle hL hM hTM hunique X hLX with hp | hx
  · have hh := (le_normalizer_twoCore X).trans (ht.normalizer_le_of_ne_bot hX hp)
    rwa [hn] at hh
  · exact hx

/-- The full maximal-overgroup assertion, with only the independent centralizer branch explicit. -/
theorem lemma_2_4_11_2_of_centralizers
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hc : ∀ z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype,
      z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    IsMaximalTwoLocal (normalizer (twoCore d.H : Set G)) ∧
      {X : Subgroup G | IsMaximalTwoLocal X ∧ d.block.map d.H.subtype ≤ X} =
        {normalizer (twoCore d.H : Set G)} := by
  let L := d.block.map d.H.subtype
  have hn := lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique
  have hQne : twoCore d.H ≠ ⊥ :=
    (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hlocal : IsTwoLocal (normalizer (L : Set G)) := hn ▸
    (show IsTwoLocal (normalizer (twoCore d.H : Set G)) from
      ⟨twoCore d.H,hQne,isPGroup_pCoreIn 2 d.H,rfl⟩)
  have h := unique_maximalTwoLocal_overgroup_of_normal L ⊥ bot_le
    ⟨normalizer (L : Set G),hlocal,le_rfl⟩ (by
      intro X hX hLX
      rw [sup_bot_eq] at hLX
      exact normal_subgroupOf_of_le_normalizer
        (source_overgroup_normalizes_of_centralizers d hG T hST hsingle hL hM hTM hunique hc
          X (Chapter1.mem_H_of_isTwoLocal hX.1) hLX))
  change normalizer (twoCore d.H : Set G) = normalizer (L : Set G) at hn
  rw [hn]
  simpa only [sup_bot_eq] using h

end CFSG.Quasithin.Chapter2.LinearShadows.Single

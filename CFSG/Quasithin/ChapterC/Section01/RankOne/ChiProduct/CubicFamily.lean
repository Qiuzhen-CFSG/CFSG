module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit

/-!
# The whole normal product of a nonempty family of A₃ blocks

In a characteristic-two group of three-rank at most two, there are at most
two χ-blocks. All Sylow conjugates of every selected A₃ block therefore
form either one A₄ or two commuting, disjoint A₄ factors. Their full join
is normal and has the corresponding A₄ or A₄² model.

This retains the whole selected family rather than one block's orbit,
as required by the exceptional branch of Aschbacher–Smith 14.1.13, p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

/-- Every selected block and all of its Sylow conjugates belong to the same normal model. -/
theorem cubic_family_models {I : Type*} [Nonempty I]
    (hfit : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (T : Sylow 2 G) (L : I → Subgroup G)
    (hb : ∀ i, IsBlock (L i)) (ha : ∀ i, IsAlternatingBlock (L i) 3) :
    let N := ⨆ i, conjugateSpanBy (L i) (T : Subgroup G)
    N.Normal ∧ (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) := by
  classical
  let N := ⨆ i, conjugateSpanBy (L i) (T : Subgroup G)
  let (i : I) : (conjugateSpanBy (L i) (T : Subgroup G)).Normal :=
    (cubic_orbit_models hfit hr T (L i) (hb i) (ha i)).1
  refine ⟨inferInstance,?_⟩
  let i₀ : I := Classical.choice inferInstance
  let B := L i₀
  have hB : IsChiBlockIn B := ⟨hb i₀,Or.inr ⟨3,by decide,ha i₀⟩⟩
  have hBN : B ≤ N := (le_conjugateSpanBy B (T : Subgroup G)).trans
    (le_iSup (fun i => conjugateSpanBy (L i) (T : Subgroup G)) i₀)
  by_cases he : ∀ (i : I) (t : T), (L i).map (MulAut.conj (t : G)).toMonoidHom = B
  · have hNB : N = B := by
      apply le_antisymm ?_ hBN
      apply iSup_le
      intro i
      rw [conjugateSpanBy_eq_iSup_conj]
      exact iSup_le fun t => (he i t).le
    exact Or.inl ⟨(MulEquiv.subgroupCongr hNB).trans
      (Classical.choice (ha i₀).equiv_alternatingFour)⟩
  push Not at he
  obtain ⟨j,t,ht⟩ := he
  let C := (L j).map (MulAut.conj (t : G)).toMonoidHom
  have hCB : C ≠ B := ht
  have hC := chi_map_equiv (MulAut.conj (t : G))
    (show IsChiBlockIn (L j) from ⟨hb j,Or.inr ⟨3,by decide,ha j⟩⟩)
  have haC := Solvable.isAlternatingBlock_of_equiv ((MulAut.conj (t : G)).subgroupMap (L j)) (ha j)
  have hpair : ({B,C} : Set (Subgroup G)) = {K | IsChiBlockIn K} := by
    apply Set.eq_of_subset_of_ncard_le
    · intro K hK
      rcases Set.mem_insert_iff.mp hK with rfl | hK
      · exact hB
      · exact Set.mem_singleton_iff.mp hK ▸ hC
    · rw [Set.ncard_pair hCB.symm]
      exact card_chiBlocks_le_two hfit hr
    · exact Set.toFinite _
  have hNC : N = B ⊔ C := by
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro s
      have hm : (L i).map (MulAut.conj (s : G)).toMonoidHom ∈ ({B,C} : Set (Subgroup G)) := by
        rw [hpair]
        exact chi_map_equiv (MulAut.conj (s : G))
          ⟨hb i,Or.inr ⟨3,by decide,ha i⟩⟩
      rcases Set.mem_insert_iff.mp hm with heq | heq
      · rw [heq]; exact le_sup_left
      · rw [Set.mem_singleton_iff.mp heq]; exact le_sup_right
    · refine sup_le hBN ?_
      apply le_trans ?_ (le_iSup (fun i => conjugateSpanBy (L i) (T : Subgroup G)) j)
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun s : T => (L j).map (MulAut.conj (s : G)).toMonoidHom) t
  have hc : B ≤ centralizer (C : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (blocks_commute (blockCommutationHypothesis_of_fitting hfit) hB.1 hC.1 hCB.symm)
  have hd : Disjoint B C := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((hc y.property x hx.2).symm)
    rw [(ha i₀).center_eq_bot,mem_bot] at hz
    exact mem_bot.mpr (congrArg Subtype.val hz)
  obtain ⟨a,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hd hc
  obtain ⟨aB⟩ := (ha i₀).equiv_alternatingFour
  obtain ⟨aC⟩ := haC.equiv_alternatingFour
  exact Or.inr ⟨((MulEquiv.subgroupCongr hNC).trans a.symm).trans (aB.prodCongr aC)⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct

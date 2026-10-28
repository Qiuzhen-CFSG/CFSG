module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCoreGeometry
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotient
public import Theory.SpecificGroups.SymmetricSix.SmallOddIndexOvergroups
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The original point centralizer and its unique outside subgroup

The literal image of H in Gz/O₂(Gz) has order 36 or 72 and odd index.
The already constructed faithful six-point action and the subgroup-order
rigidity theorem force that image to be the whole quotient. As O₂(Gz) lies
in H, this gives H=Gz.

In the original quotient H/O₂(H), the normal cubic image of L₁ and the
Sylow two-subgroup generate a subgroup of order twelve. Thus L₁T has
index three in H. Every member of H_z lies between L₁T and H, while the
definition of H_z excludes L₁T because it lies in M. Therefore H_z={Gz}.

The structural calculation first assumes only O₂(LT)=V, so it is reusable
without maximality. The final source consumer obtains this core identity
from the exceptional-component and deleted-five contradiction, retaining
the genuine earlier Hypothesis 12.2.1 for the later source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.5.15(6), printed p.921. The order-72 possibility is retained until the
centralizer equality has been proved.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSix
open Section08.SourceCompletion SourcePointCoreGeometry
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (hQ : D.LT.pCoreIn 2 = D.V)
include d h e hseed hn hU hQ

private theorem original_core_card_cases : Nat.card D.QH = 32 ∨ Nat.card D.QH = 64 := by
  have hu : 32 ≤ Nat.card D.QH := by
    have hh := card_le_of_le h.UH_le_QH
    rwa [(SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1] at hh
  have hb := original_core_card_le d h e hseed hn hU hQ
  obtain ⟨n,hncard⟩ := (isPGroup_pCoreIn 2 D.H).exists_card_eq
  change Nat.card D.QH = 2 ^ n at hncard
  have hnle : n ≤ 6 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ n)
    rw [←hncard] at hpow
    omega
  interval_cases n <;> norm_num only at hncard <;> omega

private theorem point_core_card_cases :
    Nat.card (D.Gz.pCoreIn 2) = 32 ∨ Nat.card (D.Gz.pCoreIn 2) = 64 := by
  have hi := (center (D.Gz.pCoreIn 2)).card_mul_index
  rw [index_eq_card,point_core_central_quotient_card d h e hseed hn hU hQ] at hi
  rcases point_core_center_card d h e hseed hn hU hQ with hc | hc
  · exact Or.inl (by rw [hc] at hi; omega)
  · exact Or.inr (by rw [hc] at hi; omega)

private theorem original_point_quotient_image_card :
    let q := QuotientGroup.mk' (pCore 2 D.Gz)
    Nat.card ((D.H.subgroupOf D.Gz).map q) = 36 ∨
      Nat.card ((D.H.subgroupOf D.Gz).map q) = 72 := by
  let P := D.Gz.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 D.Gz)
  let H₀ := D.H.subgroupOf D.Gz
  let B := H₀.map q
  have hPH : pCore 2 D.Gz ≤ H₀ := by
    intro x hx
    exact (pCoreIn_le 2 D.H) (SourceCentralizerCore.point_core_le_core h (mem_map_of_mem D.Gz.subtype hx))
  have hm := relIndex_mul_relIndex (⊥ : Subgroup D.Gz) (pCore 2 D.Gz) H₀ bot_le hPH
  rw [relIndex_bot_left,relIndex_bot_left,
    ←QuotientGroup.ker_mk' (pCore 2 D.Gz),relIndex_ker,QuotientGroup.ker_mk'] at hm
  have hPcard : Nat.card (pCore 2 D.Gz) = Nat.card P :=
    (card_map_of_injective D.Gz.subtype_injective).symm
  have hHcard : Nat.card H₀ = Nat.card D.H :=
    Nat.card_congr (subgroupOfEquivOfLe h.H_centralizes).toEquiv
  change Nat.card (pCore 2 D.Gz) * Nat.card B = Nat.card H₀ at hm
  rw [hPcard,hHcard] at hm
  have hlo : Nat.card P ≤ Nat.card D.QH :=
    card_le_of_le (SourceCentralizerCore.point_core_le_core h)
  have hs := (pCore 2 D.H).card_mul_index
  have hqc : Nat.card (pCore 2 D.H) = Nat.card D.QH :=
    (card_map_of_injective D.H.subtype_injective).symm
  rw [index_eq_card,hqc,SourceStarFull.original_star_card d h e hseed hn hU
    hQ] at hs
  change Nat.card B = 36 ∨ Nat.card B = 72
  rcases point_core_card_cases d h e hseed hn hU hQ with hp | hp <;>
    change Nat.card P = _ at hp <;>
    rcases original_core_card_cases d h e hseed hn hU hQ with hc | hc <;>
    rw [hp] at hm hlo <;> rw [hc] at hlo hs <;> omega

omit d e hseed hn hU hQ in
private theorem original_point_quotient_image_odd_index :
    Odd (((D.H.subgroupOf D.Gz).map (QuotientGroup.mk' (pCore 2 D.Gz))).index) := by
  let q := QuotientGroup.mk' (pCore 2 D.Gz)
  have hPH : pCore 2 D.Gz ≤ D.H.subgroupOf D.Gz := by
    intro x hx
    exact (pCoreIn_le 2 D.H) (SourceCentralizerCore.point_core_le_core h (mem_map_of_mem D.Gz.subtype hx))
  rw [(D.H.subgroupOf D.Gz).index_map_eq (QuotientGroup.mk'_surjective _) (by
    rw [QuotientGroup.ker_mk']; exact hPH)]
  let T := D.T.subtype (h.T_le_H.trans h.H_centralizes)
  have ht : (T : Subgroup D.Gz) ≤ D.H.subgroupOf D.Gz := fun x hx => h.T_le_H hx
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  exact fun hd => T.not_dvd_index (hd.trans (index_dvd_of_le ht))

theorem original_eq_point_group : D.H = D.Gz := by
  let q := QuotientGroup.mk' (pCore 2 D.Gz)
  let H₀ := D.H.subgroupOf D.Gz
  let B := H₀.map q
  obtain ⟨f,hf⟩ := point_group_six_action d h e hseed hn hU hQ
  have hB : B = ⊤ :=
    Theory.SpecificGroups.SymmetricSix.eq_top_of_odd_index_of_card_eq_thirtySix_or_seventyTwo
      f hf B (original_point_quotient_image_card d h e hseed hn hU hQ)
      (original_point_quotient_image_odd_index h)
  have hk : q.ker ≤ H₀ := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact (pCoreIn_le 2 D.H) (SourceCentralizerCore.point_core_le_core h (mem_map_of_mem D.Gz.subtype hx))
  have he : H₀ = ⊤ := by
    have hh := congrArg (fun S : Subgroup (D.Gz ⧸ pCore 2 D.Gz) => S.comap q) hB
    rw [comap_map_eq,sup_eq_left.mpr hk,comap_top] at hh
    exact hh
  have hh := congrArg (fun S : Subgroup D.Gz => S.map D.Gz.subtype) he
  rw [map_subgroupOf_eq_of_le h.H_centralizes,←MonoidHom.range_eq_map,D.Gz.range_subtype] at hh
  exact hh

theorem local_join_index : (D.L₁ ⊔ (D.T : Subgroup G)).relIndex D.H = 3 := by
  let K := D.L₁ ⊔ (D.T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 D.H)
  let A := Section08.Source.starImage D.H D.L₁
  let T := D.T.subtype h.T_le_H
  let R : Sylow 2 (Section08.Source.Hstar D.H) :=
    T.mapSurjective (QuotientGroup.mk'_surjective _)
  let : (D.L₁.subgroupOf D.H).Normal := hn
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hstar := SourceStarFull.original_star_card d h e hseed hn hU
    hQ
  have hA : Nat.card A = 3 := by
    obtain ⟨f⟩ := SourceStar.original_star_cyclic d h e hn
    rw [Nat.card_congr f.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hR : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity,hstar]
    decide +kernel
  have hdis : Disjoint A (R : Subgroup (Section08.Source.Hstar D.H)) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) _ _
      (IsPGroup.of_card (n := 1) (by simpa using hA)) R.isPGroup'
  have hcard : Nat.card (A ⊔ (R : Subgroup (Section08.Source.Hstar D.H)) : Subgroup (Section08.Source.Hstar D.H)) = 12 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A R
      (by rw [A.normalizer_eq_top]; exact le_top) hdis,hA,hR]
  have hindex : (A ⊔ (R : Subgroup (Section08.Source.Hstar D.H))).index = 3 := by
    have hm := (A ⊔ (R : Subgroup (Section08.Source.Hstar D.H))).card_mul_index
    rw [hcard,hstar] at hm
    omega
  have hk : q.ker ≤ K.subgroupOf D.H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact mem_sup_right (h.QH_le_T (mem_map_of_mem D.H.subtype hx))
  have him : (K.subgroupOf D.H).map q = A ⊔ (R : Subgroup (Section08.Source.Hstar D.H)) := by
    rw [show K = D.L₁ ⊔ (D.T : Subgroup G) from rfl,
      subgroupOf_sup (le_sup_left.trans h.local_le) h.T_le_H,Subgroup.map_sup]
    rfl
  change (K.subgroupOf D.H).index = 3
  rw [←(K.subgroupOf D.H).index_map_eq (QuotientGroup.mk'_surjective _) hk,him]
  exact hindex

omit hQ in
theorem original_not_le_maximal : ¬D.H ≤ M := by
  intro hm
  have hNV := SourceExceptionalQuotient.original_maximal_normalizes_module d h e hseed hn hU
  have hUV : D.UH ≤ D.V := conjugateSpanBy_le h.plus_le (hm.trans hNV)
  let : IsElementaryAbelian 2 D.V := h.elementary
  exact hU (IsElementaryAbelian.of_le (p := 2) hUV).toIsMulCommutative

omit hQ in
theorem original_mem_point_family :
    D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M := by
  refine ⟨⟨?_,h.local_le⟩,h.H_centralizes,original_not_le_maximal d h e hseed hn hU⟩
  intro hcore
  have hUb : D.UH = ⊥ := bot_unique (h.UH_le_QH.trans hcore.le)
  have hc := (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1
  rw [hUb,card_bot] at hc
  contradiction

theorem point_family_eq_singleton_of_original_eq (hHG : D.H = D.Gz) :
    Section08.Source.Hz D.L₁ D.T D.Gz M = {D.Gz} := by
  apply Set.Subset.antisymm
  · intro J hJ
    have hKJ : D.L₁ ⊔ (D.T : Subgroup G) ≤ J := hJ.1.2
    have hJH : J ≤ D.H := hJ.2.1.trans hHG.ge
    have hKM : D.L₁ ⊔ (D.T : Subgroup G) ≤ M := by
      rw [d.local_normalizer]
      exact sup_le (((map_subtype_le _).trans inf_le_left).trans D.L.le_normalizer) d.normalizes_L
    have hmaximal : IsCoatom ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H) :=
      isCoatom_of_index_three _ (local_join_index d h e hseed hn hU hQ)
    have hle := subgroupOf_mono D.H hKJ
    rcases hmaximal.le_iff.mp hle with ht | he
    · have hh := congrArg (fun S : Subgroup D.H => S.map D.H.subtype) ht
      rw [map_subgroupOf_eq_of_le hJH,←MonoidHom.range_eq_map,D.H.range_subtype] at hh
      exact Set.mem_singleton_iff.mpr (hh.trans hHG)
    · have hh := congrArg (fun S : Subgroup D.H => S.map D.H.subtype) he
      rw [map_subgroupOf_eq_of_le hJH,map_subgroupOf_eq_of_le h.local_le] at hh
      exact (hJ.2.2 (hh.le.trans hKM)).elim
  · rintro J (rfl : J = D.Gz)
    simpa only [hHG] using original_mem_point_family d h e hseed hn hU

/-- The point centralizer and its original outside family after the core equality. -/
theorem source13_5_15_six_of_core_eq_module :
    D.H = D.Gz ∧ Section08.Source.Hz D.L₁ D.T D.Gz M = {D.Gz} := by
  have hh := original_eq_point_group d h e hseed hn hU hQ
  exact ⟨hh, point_family_eq_singleton_of_original_eq d h e hseed hn hU hQ hh⟩

omit hQ in
/-- Source conclusion (6), with the core equality supplied by the original
exceptional component and deleted-five contradiction. -/
theorem source13_5_15_six
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    D.H = D.Gz ∧ Section08.Source.Hz D.L₁ D.T D.Gz M = {D.Gz} :=
  source13_5_15_six_of_core_eq_module d h e hseed hn hU
    (SourceExceptionalQuotient.original_core_eq_module d hmax h e hseed hn hU)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSix

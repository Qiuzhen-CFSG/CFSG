module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Placement
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Transport
public import Theory.GroupTheory.ComponentTwoCore.Normalizer
public import Theory.SpecificGroups.SL2.PairedInnerCore
public import Theory.GroupTheory.ComponentTwoCore.Product

/-!
# The original paired linear maximal two-core lies in the residual

A nontrivial odd Borel element prevents factor displacement. The binary
semilinear actor detector makes each factor action inner; triviality of the
centralizer of the paired residual then places O₂(M) in that residual.
All Borels and components are the literal original source subgroups.

Source: Aschbacher–Smith E.2.7, printed p.219.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {G : Type*} [Group G] [Finite G]

private theorem linear_normalizer_twoPerfect
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (e : G ≃* SL(2,F)) (S : Sylow 2 G) :
    IsPPerfect 2 (normalizer (S : Set G)) := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) (SpecialLinearGroup.upperUnipotentSylow F 2) Q
  have hU : (SpecialLinearGroup.upperUnipotent F).map (MulAut.conj g).toMonoidHom =
      (Q : Subgroup SL(2,F)) := congrArg (fun P : Sylow 2 SL(2,F) => P.toSubgroup) hg
  have hB : (SpecialLinearGroup.rankOneBorel F).map (MulAut.conj g).toMonoidHom =
      normalizer (Q : Set SL(2,F)) := by
    rw [SpecialLinearGroup.rankOneBorel,Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hU]
    rfl
  let d := ((MulAut.conj g).subgroupMap (SpecialLinearGroup.rankOneBorel F)).trans
    (MulEquiv.subgroupCongr hB)
  have hpQ := (SpecialLinearGroup.rankOneBorel_isPPerfect hq).of_surjective d.toMonoidHom d.surjective
  have he : (normalizer (S : Set G)).map e.toMonoidHom = normalizer (Q : Set SL(2,F)) := by
    change (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom = _
    rw [Subgroup.map_normalizer_eq_of_bijective (S : Subgroup G) e.bijective]
    rfl
  let a := (e.subgroupMap (normalizer (S : Set G))).trans (MulEquiv.subgroupCongr he)
  exact hpQ.of_surjective a.symm.toMonoidHom a.symm.surjective

theorem core_normalizes_linear_component
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hK : IsComponent G K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hrad : solvableRadical G = ⊥)
    (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (e : K ≃* SL(2,F)) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ normalizer (K : Set G) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n)
  have heven : 2 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans (b := Nat.card (SpecialLinearGroup.upperUnipotent F))
    · rw [SpecialLinearGroup.card_upperUnipotent F,hF]
      exact dvd_pow_self 2 (by omega)
    · exact card_subgroup_dvd_card _
  have hm : ChapterF.Source.IsRankOneModel K := .linear n (by omega)
    ⟨F,inferInstance,inferInstance,hF,⟨e.trans (SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F)⟩⟩
  have hb := component_borel_intersection T hP K hK heven ho hm
  let M := ChapterB.minimalParabolicMax T hP
  let B := (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype
  have hBM : B ≤ M := by
    change (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M
    rw [← hb]
    exact (subgroupOf_map_subtype M K).le.trans inf_le_left
  have hBn : B ≠ ⊥ := by
    intro hz
    apply component_sylow_intersection_ne_bot T hK heven
    have hn : normalizer ((T : Subgroup G).subgroupOf K : Set K) = ⊥ :=
      (Subgroup.map_injective K.subtype_injective) (hz.trans (Subgroup.map_bot _).symm)
    exact le_bot_iff.mp (hn ▸ ((T : Subgroup G).subgroupOf K).le_normalizer)
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hp : IsPPerfect 2 (normalizer ((T : Subgroup G).subgroupOf K : Set K)) := by
    rw [← hS]
    exact linear_normalizer_twoPerfect hq e S
  have hpB : IsPPerfect 2 B := hp.of_surjective
    (K.subtype.subgroupMap (normalizer ((T : Subgroup G).subgroupOf K : Set K)))
    (K.subtype.subgroupMap_surjective _)
  exact pCoreIn_le_component_normalizer_of_pPerfect M K B hK hC hrad
    (map_subtype_le _) hBM hBn hpB

theorem core_le_linear_component_centralizer
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hK : IsComponent G K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hrad : solvableRadical G = ⊥)
    (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    (e : K ≃* SL(2,F)) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ K ⊔ centralizer (K : Set G) := by
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  have hm : ChapterF.Source.IsRankOneModel K := .linear n (by omega)
    ⟨F,inferInstance,inferInstance,hF,⟨e.trans (SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F)⟩⟩
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hB : (ChapterB.minimalParabolicMax T hP).subgroupOf K = normalizer (S : Set K) := by
    change (ChapterB.minimalParabolicMax T hP).subgroupOf K =
      normalizer ((S : Subgroup K) : Set K)
    rw [hS]
    exact component_borel_intersection T hP K hK heven ho hm
  exact ProjectiveSpecialLinearGroup.normalizing_borel_twoCore_le_sup_centralizer hF K
    (e.trans (SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F)) T _
    (ChapterB.minimalParabolicMax_spec T hP).2 S hS hB
    (core_normalizes_linear_component hn hF T hP K hK hC hrad ho e)

theorem source_linear_core_le_residual
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hH : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable G)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup G} (hK : IsComponent G K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K ⊔ (T : Subgroup G) = ⊤) (hnot : ¬ K.Normal)
    (e : K ≃* SL(2,F)) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ pResidual 2 G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have ho := Structure.generating_component_orbit_eq_residual hH T hK hgen
  obtain ⟨t,hne,hDsimple,hD,hR,_,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hC hgen hnot
  let D := K.map (MulAut.conj (t:G)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let : IsQuasisimple D := hD.2
  have hDC : D.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hD.1
  let eD : D ≃* SL(2,F) := ((MulAut.conj (t:G)).subgroupMap K).symm.trans e
  have hDt : D ⊔ (T : Subgroup G) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:G)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:G)).surjective] at he
    have ht : (T : Subgroup G).map (MulAut.conj (t:G)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property)
    rwa [ht] at he
  have hKo := core_le_linear_component_centralizer hn hF T hP K hK hC hrad ho e
  have hDo := core_le_linear_component_centralizer hn hF T hP D hD hDC hrad
    (Structure.generating_component_orbit_eq_residual hH T hD hDt) eD
  have hnormal : (K ⊔ D).Normal := by rw [← hR]; infer_instance
  let := hnormal
  have hRT : (K ⊔ D : Subgroup G) ⊔ (T : Subgroup G) = ⊤ := top_unique (by
    rw [← hgen]
    exact sup_le_sup le_sup_left le_rfl)
  have hZ : center (K ⊔ D : Subgroup G) = ⊥ :=
    center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad hnormal.isSubnormal
  have hCR : centralizer ((K ⊔ D : Subgroup G) : Set G) = ⊥ := by
    have hcT := centralizer_le_sylow_of_centerless_supplement (K ⊔ D) T hRT hZ
    have hcO : centralizer ((K ⊔ D : Subgroup G) : Set G) ≤ pCore 2 G :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hcT⟩
    exact le_bot_iff.mp (hcO.trans ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans hJ.le))
  rw [hR]
  exact (le_inf hKo hDo).trans (inf_inner_centralizer_supplements_le_sup K D
    (hK.commutator_eq_bot_of_ne hD hne.symm) hCR)
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender

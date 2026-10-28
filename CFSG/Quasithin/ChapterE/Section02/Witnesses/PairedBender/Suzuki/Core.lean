module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Placement
public import Theory.GroupTheory.ComponentTwoCore.Normalizer
public import Theory.GroupTheory.ComponentTwoCore.Product
public import Theory.SpecificGroups.Suzuki.NormalSupplement
public import Theory.SpecificGroups.Suzuki.BorelResidual
/-!
# Placement of the original paired Suzuki two-core

A nontrivial two-perfect component Borel prevents O₂(M) from exchanging
components. The Suzuki outer automorphism group has odd order, so the
two-core acts by inner automorphisms on both factors. Their residual has
trivial centralizer in the core-free source group; hence O₂(M) lies in
the product of those actual factors. No placement premise is used.

Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_twoPerfect {m : ℕ} (hm : 0<m)
    (e : G ≃* SuzukiMatrixGroup m) (S : Sylow 2 G) :
    IsPPerfect 2 (normalizer (S : Set G)) := by
  obtain ⟨f,_,hb⟩ := suzukiSylow_aligned_equiv hm e S
  let d := (f.subgroupMap (SuzukiBorelSubgroup m)).trans (MulEquiv.subgroupCongr hb)
  exact ((pResidual_eq_top_iff 2 _).mp (suzukiBorel_pResidual_eq_top m hm)).of_surjective
    d.toMonoidHom d.surjective

omit [Finite G] in
private theorem core_inner_of_normalizes (M K : Subgroup G)
    (hQN : M.pCoreIn 2 ≤ normalizer (K : Set G)) {m : ℕ}
    (hm : 0<m) (e : K ≃* SuzukiMatrixGroup m) :
    M.pCoreIn 2 ≤ K ⊔ centralizer (K : Set G) := by
  let f : M.pCoreIn 2 →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (K.normalizerMonoidHom.comp (inclusion hQN))
  have hodd : Odd (Nat.card (MulAut.Outer K)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact suzuki_odd_outer_index m (by omega)
  intro x hx
  let v : M.pCoreIn 2 := ⟨x,hx⟩
  obtain ⟨r,hr⟩ := isPGroup_pCoreIn 2 M v
  have hpow : f v ^ (2^r) = 1 := by rw [←map_pow,hr,map_one]
  have hfo : f v = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_right.pow_right r) (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one hpow))
  have hi : K.normalizerMonoidHom (inclusion hQN v) ∈ MulAut.innerSubgroup K :=
    (QuotientGroup.eq_one_iff _).mp hfo
  obtain ⟨k,hk⟩ := hi
  let kN : normalizer (K : Set G) := ⟨k,K.le_normalizer k.property⟩
  have hkN : K.normalizerMonoidHom kN = MulAut.conj k := by ext y; rfl
  have hz : kN⁻¹ * inclusion hQN v ∈ K.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hkN,hk,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hz
  have hh := (K ⊔ centralizer (K : Set G)).mul_mem
    (mem_sup_left k.property) (mem_sup_right (show (k:G)⁻¹*x ∈ centralizer (K:Set G) from hz))
  simpa only [mul_inv_cancel_left] using hh

/-- The original maximal two-core preserves the actual Suzuki component. -/
theorem core_normalizes_component
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hK : IsComponent G K) [IsSimpleGroup K]
    (hrad : solvableRadical G = ⊥)
    (ho : componentOrbit K (T : Subgroup G) = pResidual 2 G)
    {m : ℕ} (hm : 0<m) (e : K ≃* SuzukiMatrixGroup m) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ normalizer (K : Set G) := by
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K
      (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)))
  have hmodel : ChapterF.Source.IsRankOneModel K := .suzuki m ⟨e⟩
  have hb := component_borel_intersection T hP K hK heven ho hmodel
  let M := ChapterB.minimalParabolicMax T hP
  let B := (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype
  have hBM : B ≤ M := by
    change (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M
    rw [←hb]
    exact (subgroupOf_map_subtype M K).le.trans inf_le_left
  have hBn : B ≠ ⊥ := by
    intro hz
    apply component_sylow_intersection_ne_bot T hK heven
    have hn : normalizer ((T : Subgroup G).subgroupOf K : Set K) = ⊥ :=
      (Subgroup.map_injective K.subtype_injective) (hz.trans (Subgroup.map_bot _).symm)
    exact le_bot_iff.mp (hn ▸ ((T : Subgroup G).subgroupOf K).le_normalizer)
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hp : IsPPerfect 2 (normalizer ((T : Subgroup G).subgroupOf K : Set K)) := by
    rw [←hS]
    exact normalizer_twoPerfect hm e S
  have hpB : IsPPerfect 2 B := hp.of_surjective
    (K.subtype.subgroupMap (normalizer ((T : Subgroup G).subgroupOf K : Set K)))
    (K.subtype.subgroupMap_surjective _)
  exact pCoreIn_le_component_normalizer_of_pPerfect M K B hK hK.isCComponent hrad
    (map_subtype_le _) hBM hBn hpB

/-- Odd outer action on both factors places the original two-core in the residual. -/
theorem source_core_le_residual
    (hH : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable G)
    (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hnot : ¬ K.Normal)
    {m : ℕ} (hm : 0<m) (e : K ≃* SuzukiMatrixGroup m) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ pResidual 2 G := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have ho := Structure.generating_component_orbit_eq_residual hH T hK hgen
  obtain ⟨t,hne,hDsimple,hD,hR,_,_,_⟩ :=
    Structure.source_pair_coordinates hH T hP hs hJ hK hK.isCComponent hgen hnot
  let D := K.map (MulAut.conj (t:G)).toMonoidHom
  let : IsSimpleGroup D := hDsimple
  let eD : D ≃* SuzukiMatrixGroup m := ((MulAut.conj (t:G)).subgroupMap K).symm.trans e
  have hDt : D ⊔ (T : Subgroup G) = ⊤ := by
    have he := congrArg (Subgroup.map (MulAut.conj (t:G)).toMonoidHom) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj (t:G)).surjective] at he
    have ht : (T : Subgroup G).map (MulAut.conj (t:G)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property)
    rwa [ht] at he
  have hKo := core_inner_of_normalizes _ K (core_normalizes_component T hP K hK hrad ho hm e) hm e
  have hDo := core_inner_of_normalizes _ D (core_normalizes_component T hP D hD hrad
    (Structure.generating_component_orbit_eq_residual hH T hD hDt) hm eD) hm eD
  have hnormal : (K ⊔ D).Normal := by rw [←hR]; infer_instance
  let := hnormal
  have hRT : (K ⊔ D : Subgroup G) ⊔ (T : Subgroup G) = ⊤ := top_unique (by
    rw [←hgen]
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
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki

module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.CentralizerBound
public import Theory.GroupAction.IndexTwoIntersectionCore
public import Theory.ElementaryAbelian.GeneratorRank
/-!
# The original C.6 centralizer rank bounds

The source terminal identities identify C_R(K) with its Baumann intersection.
The intersection with its conjugate is normalized by the actual index-two
overgroup and by H; the original common-normal obstruction kills it.
The intrinsic core-pair estimate now gives |C_R(K)|≤2ⁿ and two-rank at most n
for a natural L₂(2ⁿ) block, and order at most two in the single A₃ case.

Source: Aschbacher--Smith C.6.1(3), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

theorem rankOne_centralizer_card_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ Nat.card F ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hphi := h.frattini_eq_bot_of_index_two H M R c.T_le c.R_normal hRK hH hno hi x hx hnc
  have he := h.source_single_block_terminal_equalities c.R_twoGroup H M R le_rfl c.T_le
    c.R_normal hRK hH hno x hx hi hnc
  have hD : R ⊓ centralizer (K : Set G) = RankOne.D R K := he.2.2
  have hxout : x ∉ R := by
    intro hxr
    have hn := normalizer_le_normalizer_characteristic_image K (blockU K) (hRK hxr)
    have hm : (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom = sourceModule K :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (sourceModule K : Set G)).inv_mem hn)
    apply hnc
    rw [hm]
    let := h.elementary
    exact le_centralizer (RankOne.U K)
  let D := RankOne.D R K
  have hnC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hRD : R ≤ normalizer (D : Set G) :=
    (le_inf (R.le_normalizer.trans (normalizer_le_normalizer_baumann R))
      (hRK.trans hnC)).trans inf_normalizer_le_normalizer_inf
  let I := D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom
  have hMI : M ≤ normalizer (I : Set G) :=
    index_two_conjugate_intersection_normalized M R D c.R_le_M hi hRD x hx hxout
  have hKI : K ≤ normalizer (I : Set G) :=
    (le_centralizer_iff.mp (show I ≤ centralizer (K : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hI : I = ⊥ := hno I (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (hH ▸ sup_le hKI (c.R_le_M.trans hMI)) hMI
  let : IsElementaryAbelian 2 (RankOne.Q R K) := h.core_elementary (c.R_normal hx) hnc hphi
  have hd : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le
    (show D ≤ RankOne.Q R K from (h.factorization (c.R_normal hx) hnc).core ▸ le_sup_right)
  change IsElementaryAbelian 2 (R ⊓ centralizer (K : Set G) : Subgroup G) ∧ _
  rw [hD]
  exact ⟨hd,h.centralizer_card_bound (c.R_normal hx) hnc hphi hI,hI⟩

theorem natural_centralizer_rank_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    {n : ℕ} (hK : IsL2EvenBlock K n)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ 2 ^ n ∧ primeRank 2 D ≤ n := by
  have hh := rankOne_centralizer_card_from_original c h hi x hx hnc
  let := hh.1
  have hc : Nat.card (R ⊓ centralizer (K : Set G) : Subgroup G) ≤ 2 ^ n :=
    hh.2.1.trans_eq (h.coordinates.field_card_of_linear hK)
  exact ⟨hh.1,hc,IsElementaryAbelian.primeRank_le_of_card_le _ hc⟩

theorem cubic_centralizer_rank_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K : Set G)
    IsElementaryAbelian 2 D ∧ Nat.card D ≤ 2 ∧ primeRank 2 D ≤ 1 := by
  have hh := rankOne_centralizer_card_from_original c h hi x hx hnc
  let := hh.1
  have hc : Nat.card (R ⊓ centralizer (K : Set G) : Subgroup G) ≤ 2 :=
    hh.2.1.trans_eq (h.coordinates.field_card_of_cubic hK)
  exact ⟨hh.1,hc,IsElementaryAbelian.primeRank_le_of_card_le _ (by simpa using hc)⟩
end CFSG.Quasithin.ChapterC.Section06

module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.ElementaryThompsonComponent
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Thompson commutators in the escaping configuration

For J=J_j(R), heredity at JO₂(Y) excludes [Y,J]≤O₂(Y) when Y escapes a
subgroup controlling N_G(J). The Frattini argument at [Y,J]J gives
Y=[Y,J]N_Y(J), so the actual commutator also escapes. All statements retain
relative Sylow membership in YR. Normalizer control itself rules out the
zero Thompson subgroup, discharging the index bound at the consumer.

The choice of j and its controlled normalizer remain part of the later
13.1.9 assembly in qt-d-1319-ff-contradiction. No idempotence of [Y,J], FF
inequality, or representation classification is assumed or asserted here.
Source: Aschbacher--Smith 13.1.9, printed p.870, using B.2.3(3), p.75.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
open scoped Pointwise

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
variable {G : Type*} [Group G] [Finite G]

/-- Normalizers preserve every rank-indexed Thompson subgroup. -/
theorem normalizer_le_thompson (R : Subgroup G) (j : ℕ) :
    normalizer (R : Set G) ≤ normalizer (thompsonJ R j : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ R j).map (MulAut.conj g).toMonoidHom = thompsonJ R j
  have he : R.map (MulAut.conj g).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg
  rw [← thompsonJ_map_equiv,he]

omit [Finite G] in
private theorem normalizes_join (Y J C : Subgroup G)
    (hYC : Y ≤ normalizer (C : Set G)) (hc : ⁅Y,J⁆ ≤ C) :
    Y ≤ normalizer ((J ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  exact commutator_sup_le_of_relative_normal (J ⊔ C) J C Y (J ⊔ C)
    (J ⊔ C).le_normalizer le_sup_left le_sup_right
    ((commutator_comm J Y).le.trans (hc.trans le_sup_right))
    ((le_normalizer_iff_commutator_le_left.mp hYC).trans le_sup_right)

/-- A controlled normalizer and an escaping subgroup force a nondegenerate
Thompson index. No additional source rank hypothesis is needed. -/
theorem thompson_index_lt_of_normalizer_control (Y R M : Subgroup G) {j : ℕ}
    (hout : ¬ Y ≤ M) (hN : normalizer (thompsonJ R j : Set G) ≤ M) :
    j < twoRank R := by
  by_contra hj
  have hr : twoRank R ≤ j := Nat.le_of_not_gt hj
  have he : thompsonJ R j = ⊥ := by
    apply bot_unique
    apply sSup_le
    intro A hA
    exact (Subgroup.card_eq_one.mp (by
      rw [hA.2.2.2,Nat.sub_eq_zero_of_le hr,pow_zero])).le
  rw [he,normalizer_eq_top] at hN
  exact hout (le_top.trans hN)

/-- Heredity at J_j(R)O₂(Y) rules out a commutator confined to O₂(Y). -/
theorem thompson_commutator_not_le_core (Y R M : Subgroup G) {j : ℕ}
    (hj : j < twoRank R) (hcore : Y.pCoreIn 2 ≤ R)
    (hout : ¬ Y ≤ M) (hN : normalizer (thompsonJ R j : Set G) ≤ M) :
    ¬ ⁅Y,thompsonJ R j⁆ ≤ Y.pCoreIn 2 := by
  intro hc
  let J := thompsonJ R j
  let R₁ := J ⊔ Y.pCoreIn 2
  have hYR₁ : Y ≤ normalizer (R₁ : Set G) := normalizes_join Y J (Y.pCoreIn 2)
    (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))) hc
  have hJR₁ : J = thompsonJ R₁ j := lemma_B_2_3_3 R R₁ hj le_sup_left
    (sup_le (thompsonJ_le R j) hcore)
  apply hout
  apply (hYR₁.trans (normalizer_le_thompson R₁ j)).trans
  rwa [← hJR₁]

private theorem thompson_frattini (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    {j : ℕ} (hj : j < twoRank (S : Subgroup G))
    (hJN : thompsonJ (S : Subgroup G) j ≤ N) :
    normalizer (thompsonJ (S : Subgroup G) j : Set G) ⊔ N = ⊤ := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let Q := (P : Subgroup N).map N.subtype
  have hQ : Q = (S : Subgroup G) ⊓ N := by
    rw [show Q = (P : Subgroup N).map N.subtype from rfl,hP,subgroupOf_map_subtype]
  have hJQ : thompsonJ (S : Subgroup G) j = thompsonJ Q j :=
    lemma_B_2_3_3 _ _ hj (hQ ▸ le_inf (thompsonJ_le _ _) hJN) (hQ ▸ inf_le_left)
  have hn : normalizer (Q : Set G) ≤ normalizer (thompsonJ (S : Subgroup G) j : Set G) := by
    rw [hJQ]
    exact normalizer_le_thompson Q j
  exact top_unique (P.normalizer_sup_eq_top.symm.le.trans (sup_le_sup_right hn N))

/-- The Frattini factorization at the normal subgroup [Y,J]J. -/
theorem thompson_commutator_factorization (S : Sylow 2 G) (Y : Subgroup G) [Y.Normal]
    (hgen : Y ⊔ (S : Subgroup G) = ⊤) {j : ℕ}
    (hj : j < twoRank (S : Subgroup G)) :
    Y = ⁅Y,thompsonJ (S : Subgroup G) j⁆ ⊔
      (Y ⊓ normalizer (thompsonJ (S : Subgroup G) j : Set G)) := by
  let J := thompsonJ (S : Subgroup G) j
  let K := ⁅Y,J⁆
  have hSJ : (S : Subgroup G) ≤ normalizer (J : Set G) := le_normalizer_thompsonJ _ _
  let : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le (normalizer_commutator_ge_left Y J) ?_
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change K.map (MulAut.conj s).toMonoidHom = K
    have hJ : J.map (MulAut.conj s).toMonoidHom = J := mem_normalizer_iff_map_conj_eq.mp (hSJ hs)
    have hY : Y.map (MulAut.conj s).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (Y.normalizer_eq_top ▸ mem_top s)
    rw [map_commutator,hJ,hY]
  let N := J ⊔ K
  let : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (normalizes_join Y J K le_normalizer_of_normal le_rfl)
      (hSJ.trans normalizer_le_normalizer_sup_normal)
  have hf := thompson_frattini S N hj (show J ≤ N from le_sup_left)
  have hNK : normalizer (J : Set G) ⊔ K = ⊤ := by
    change normalizer (J : Set G) ⊔ (J ⊔ K) = ⊤ at hf
    rwa [← sup_assoc, sup_of_le_left J.le_normalizer] at hf
  apply le_antisymm
  · intro y hy
    obtain ⟨n,hn,k,hk,he⟩ := mem_sup_of_normal_right.mp (hNK.symm ▸ mem_top y)
    have hnY : n ∈ Y := by
      have h := Y.mul_mem hy (Y.inv_mem (commutator_le_left Y J hk))
      rwa [← he,mul_inv_cancel_right] at h
    rw [← he]
    exact (K ⊔ (Y ⊓ normalizer (J : Set G))).mul_mem
      (mem_sup_right ⟨hnY,hn⟩) (mem_sup_left hk)
  · exact sup_le (commutator_le_left Y J) inf_le_left

/-- The same factorization on the literal YR, with its embedded Sylow R. -/
theorem relative_thompson_commutator_factorization (Y R : Subgroup G)
    (hRY : R ≤ normalizer (Y : Set G))
    (hSyl : Chapter1.IsSylowIn 2 R (Y ⊔ R)) {j : ℕ} (hj : j < twoRank R) :
    Y = ⁅Y,thompsonJ R j⁆ ⊔ (Y ⊓ normalizer (thompsonJ R j : Set G)) := by
  let H := Y ⊔ R
  let Y₀ := Y.subgroupOf H
  let : Y₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hRY)
  obtain ⟨S,hS⟩ := hSyl
  have hjS : j < twoRank (S : Subgroup H) := by
    rwa [← twoRank_map_injective H.subtype H.subtype_injective,hS]
  have hgen : Y₀ ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Y ≤ H from le_sup_left),hS,
      ← MonoidHom.range_eq_map,range_subtype]
  have hJ : (thompsonJ (S : Subgroup H) j).map H.subtype = thompsonJ R j := by
    rw [← thompsonJ_map_injective H.subtype H.subtype_injective,hS]
  have hN : (normalizer (thompsonJ (S : Subgroup H) j : Set H)).map H.subtype ≤
      normalizer (thompsonJ R j : Set G) := by
    rw [← hJ]
    exact (thompsonJ (S : Subgroup H) j).le_normalizer_map H.subtype
  have hf := congrArg (map H.subtype) (thompson_commutator_factorization S Y₀ hgen hjS)
  rw [Subgroup.map_sup,map_commutator,
    Subgroup.map_inf _ _ H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le (show Y ≤ H from le_sup_left),hJ] at hf
  apply le_antisymm
  · exact hf.le.trans (sup_le_sup_left (inf_le_inf_left Y hN) _)
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp ((thompsonJ_le R j).trans hRY))
      inf_le_left

/-- Normalizer control makes the actual commutator escape as well. -/
theorem relative_thompson_commutator_outside (Y R M : Subgroup G)
    (hRY : R ≤ normalizer (Y : Set G))
    (hSyl : Chapter1.IsSylowIn 2 R (Y ⊔ R)) {j : ℕ} (hj : j < twoRank R)
    (hout : ¬ Y ≤ M) (hN : normalizer (thompsonJ R j : Set G) ≤ M) :
    ¬ ⁅Y,thompsonJ R j⁆ ≤ M := by
  intro hK
  apply hout
  rw [relative_thompson_commutator_factorization Y R hRY hSyl hj]
  exact sup_le hK (inf_le_right.trans hN)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction

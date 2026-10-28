module

public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupAction.CentralKernelFixedIndex
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Checked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation

/-!
# The small-index step of 13.6.17

Centrality modulo the literal kernel ⟨v⟩ bounds the centralizer index in Tᵥ
by two and hence its index in T by four. A Sylow order comparison bounds
[O₂(C_G(a)):N_{O₂(C_G(a))}(K)] by four. The perfect small-normalizer
argument then makes K normal in K O₂(C_G(a)).

The application retains the actual Y_z family and the direction of
Tᵥ-invariance. It proves this portion of 13.6.17 only. The later signalizer
transfer, conjugated Sylow subgroup and faithful-component contradiction
are still required before asserting noncentrality. Conjugacy of a and z
is needed in that later argument, not in this index calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, Lemma 13.6.17, printed p.930.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open A5Module ComponentSelection
variable {G : Type*} [Group G] [Finite G]

theorem checked_centralizer_index_le_two (T : Subgroup G) (v : G) (a : Gv v)
    (hv : v ^ 2 = 1)
    (ha : checkedQuotientMap v a ∈ centralizer (checkedImage v (Tv T v) : Set (Gcheck v))) :
    (Gv (a : G)).relIndex (Tv T v) ≤ 2 := by
  have hi := MulAut.fixedSubgroup_relIndex_le_card_kernel
    (checkedQuotientMap v) (MulAut.conj a) ((Tv T v).subgroupOf (Gv v))
    (by rw [checkedQuotientMap_kernel]; exact vLine_le_center v) (by
      intro x hx
      change checkedQuotientMap v (a * x * a⁻¹) = checkedQuotientMap v x
      rw [map_mul, map_mul, map_inv,
        ← ha _ (mem_map_of_mem _ hx), mul_inv_cancel_right])
  have hfix : (MulAut.conj a).fixedSubgroup = (Gv (a : G)).subgroupOf (Gv v) := by
    ext x
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf]
    change a * x * a⁻¹ = x ↔ (x : G) ∈ Gv (a : G)
    rw [mul_inv_eq_iff_eq_mul]
    change a * x = x * a ↔ (x : G) ∈ centralizer ({(a : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.trans eq_comm
  rw [hfix, relIndex_subgroupOf (show Tv T v ≤ Gv v from inf_le_right)] at hi
  apply hi.trans
  rw [checkedQuotientMap_kernel]
  change Nat.card (zpowers (centralElement v)) ≤ 2
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one (show centralElement v ^ 2 = 1 from Subtype.ext hv))

theorem checked_centralizer_index_le_four (T : Subgroup G) (v : G) (a : Gv v)
    (hv : v ^ 2 = 1) (hidx : (Tv T v).relIndex T = 2)
    (ha : checkedQuotientMap v a ∈ centralizer (checkedImage v (Tv T v) : Set (Gcheck v))) :
    ((Tv T v) ⊓ Gv (a : G)).relIndex T ≤ 4 := by
  have hi := checked_centralizer_index_le_two T v a hv ha
  have hm := relIndex_mul_relIndex ((Tv T v) ⊓ Gv (a : G)) (Tv T v) T
    inf_le_left inf_le_left
  rw [inf_relIndex_left, hidx] at hm
  omega

private theorem core_normalizer_index_le (T : Sylow 2 G) (a : G)
    (C K : Subgroup G) (hCT : C ≤ T) (hCa : C ≤ Gv a)
    (hCK : C ≤ normalizer (K : Set G)) :
    (normalizer (K : Set G)).relIndex (Qv a) ≤ C.relIndex (T : Subgroup G) := by
  have hCQ : C ≤ normalizer (Qv a : Set G) := hCa.trans
    ((Gv a).le_normalizer.trans (normalizer_le_normalizer_characteristic_image
      (Gv a) (pCore 2 (Gv a))))
  have hp : IsPGroup 2 ((Qv a) ⊔ C : Subgroup G) :=
    (isPGroup_pCoreIn 2 (Gv a)).to_sup_of_normal_left'
      (T.isPGroup'.to_le hCT) hCQ
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hc : Nat.card ((Qv a) ⊔ C : Subgroup G) ≤ Nat.card (T : Subgroup G) := by
    exact (card_le_of_le hP).trans_eq (Nat.card_congr (P.equiv T).toEquiv)
  have hmul₁ := relIndex_mul_relIndex (⊥ : Subgroup G) C ((Qv a) ⊔ C)
    bot_le le_sup_right
  have hmul₂ := relIndex_mul_relIndex (⊥ : Subgroup G) C (T : Subgroup G) bot_le hCT
  simp only [relIndex_bot_left, relIndex_sup_of_normalizes_left (Qv a) C hCQ] at hmul₁ hmul₂
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hidx : C.relIndex (Qv a) ≤ C.relIndex (T : Subgroup G) := by nlinarith
  exact (relIndex_le_of_le_left hCK index_ne_zero_of_finite).trans hidx

theorem normalizer_twoCore_index_le_four (T : Sylow 2 G) (K : Subgroup G)
    (v : G) (a : Gv v) (hv : v ^ 2 = 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (ha : checkedQuotientMap v a ∈ centralizer
      (checkedImage v (Tv (T : Subgroup G) v) : Set (Gcheck v))) :
    (normalizer (K : Set G)).relIndex (Qv (a : G)) ≤ 4 := by
  exact (core_normalizer_index_le T (a : G) (Tv (T : Subgroup G) v ⊓ Gv (a : G)) K
    (inf_le_left.trans inf_le_left) inf_le_right (inf_le_left.trans hTK)).trans
    (checked_centralizer_index_le_four (T : Subgroup G) v a hv hidx ha)

theorem normal_in_sup_twoCore_of_checked_centralizes
    (T : Sylow 2 G) (L K : Subgroup G) (z v : G) (a : Gv v)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hv : v ^ 2 = 1)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (ha : checkedQuotientMap v a ∈ centralizer
      (checkedImage v (Tv (T : Subgroup G) v) : Set (Gcheck v)))
    (hKa : K ≤ Gv (a : G)) :
    (K.subgroupOf (K ⊔ Qv (a : G))).Normal := by
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.1.2
  have hp : IsPGroup 2 (Qv (a : G)) := isPGroup_pCoreIn 2 (Gv (a : G))
  let : Group.IsNilpotent (Qv (a : G)) := hp.isNilpotent
  apply normal_in_sup_of_perfect_of_solvable_of_small_normalizer K (Qv (a : G))
  · exact hKa.trans ((Gv (a : G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (Gv (a : G)) (pCore 2 (Gv (a : G)))))
  · exact normalizer_twoCore_index_le_four T K v a hv hidx hTK ha
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields

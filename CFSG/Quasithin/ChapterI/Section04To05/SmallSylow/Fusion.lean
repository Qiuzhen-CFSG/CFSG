module

public import ABG.ChapterII.Section1.Fusion
public import ABG.ChapterII.Section1.FusionFrame
public import Theory.GroupTheory.PGroup.MaximalIndex
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.CyclicSylowTwoOddOrder

/-!
# Fusion in the semidihedral source branch

The full ABG II.1 fusion alternatives apply to actual four and quaternion
subgroups in the specified semidihedral Sylow subgroup. The two index-two
alternatives contradict the original source hypothesis. A normal odd
complement would also give an index-two subgroup, since the Sylow subgroup
is nontrivial. The remaining alternative gives one class of involutions
and one class of order-four elements.

This discharges the fusion step in Aschbacher–Smith I.4.3, printed p.416,
using the proved ABG II.1 Proposition 1 rather than redoing transfer.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterI.SmallSylow
variable {G : Type*} [Group G] [Finite G]
private theorem no_normal_complement_of_no_index_two
    (T : Sylow 2 G) (hT : Even (Nat.card T))
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ¬ HasNormalPComplement 2 G := by
  rintro ⟨N, hN, hodd, hQ⟩
  let := hN
  have hcard : Even (Nat.card (G ⧸ N)) := by
    have hG : Even (Nat.card G) := hT.trans_dvd T.card_subgroup_dvd_card
    have hm := N.card_mul_index
    have hNo : Odd (Nat.card N) := Nat.coprime_two_left.mp hodd
    rw [← hm, Nat.even_mul] at hG
    exact hG.resolve_left (Nat.not_even_iff_odd.mpr hNo)
  have hne : Nontrivial (G ⧸ N) := by
    apply (Finite.one_lt_card_iff_nontrivial).mp
    have hp := Nat.card_pos (α := G ⧸ N)
    have he := hcard.two_dvd
    omega
  let := hne
  obtain ⟨U, hU⟩ := IsCoatomic.exists_coatom (α := Subgroup (G ⧸ N))
  let q := QuotientGroup.mk' N
  have hi : (U.comap q).index = 2 :=
    (U.index_comap_of_surjective (QuotientGroup.mk'_surjective N)).trans
      (hQ.index_of_isCoatom U hU)
  exact hno (U.comap q) ((U.comap q).normal_of_index_eq_two hi) hi

/-- The original no-index-two hypothesis gives single classes of involutions and order-four elements. -/
public theorem semidihedral_fusion
    (T : Sylow 2 G) (hT : Stellmacher.IsSemidihedralGroup T)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
      (∀ x y : G, orderOf x = 4 → orderOf y = 4 → IsConj x y) := by
  obtain ⟨E, Q, hf⟩ := ABG.exists_quasiDihedralFusionFrame T hT
  have hcounts : ABG.HasElementConjugacyClassCount G 2 1 ∧
      ABG.HasElementConjugacyClassCount G 4 1 := by
    rcases ABG.quasiDihedral_fusion T E Q hf with h | h | h | h
    · exact ⟨h.2.1, h.2.2.1⟩
    · obtain ⟨N, hn, hi, _⟩ := h.1
      exact (hno N hn hi).elim
    · obtain ⟨N, hn, hi, _⟩ := h.1
      exact (hno N hn hi).elim
    · apply (no_normal_complement_of_no_index_two T ?_ hno h.1).elim
      obtain ⟨n, hn, hc, _⟩ := hT
      rw [hc]
      exact even_iff_two_dvd.mpr (dvd_pow_self _ (by omega))
  have count_one (m : ℕ) (hc : ABG.HasElementConjugacyClassCount G m 1)
      (x y : G) (hx : orderOf x = m) (hy : orderOf y = m) : IsConj x y := by
    obtain ⟨r, _, _, hr⟩ := hc
    obtain ⟨i, hi⟩ := hr x hx
    obtain ⟨j, hj⟩ := hr y hy
    have he : i = j := Subsingleton.elim _ _
    exact hi.trans (he ▸ hj.symm)
  exact ⟨count_one 2 hcounts.1, count_one 4 hcounts.2⟩
end CFSG.Quasithin.ChapterI.SmallSylow

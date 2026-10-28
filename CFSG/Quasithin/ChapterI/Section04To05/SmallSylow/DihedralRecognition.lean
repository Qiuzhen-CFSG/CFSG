module

public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.DihedralLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.A5
public import Theory.GroupTheory.CyclicSylowTwoOddOrder
public import Stellmacher.MainDefs

/-!
# Dihedral Sylow recognition in even characteristic

The Sylow order forces the dihedral rotation parameter to be a power of two;
its cyclic degenerate case is excluded by transfer and the absence of an
index-two subgroup. The marked rotation involution has the original Sylow
subgroup as its full centralizer, and all involutions are conjugate to it.
I.4.1 then applies. The actual exceptional isomorphisms identify A₄, A₅ and
PSL₃(2) with PSL₂(3), PSL₂(5) and PSL₂(7), retaining the nonsimple A₄ case.

Source: Aschbacher–Smith I.4.3(1), printed pp.416–417.
-/

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterI.SmallSylow
variable {G : Type*} [Group G] [Finite G]

/-- The full finite-group dihedral conclusion of I.4.3, with no simplicity premise. -/
public theorem dihedral_recognition
    (hno : ∀ N : Subgroup G, N.index ≠ 2) (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) (hT : Stellmacher.IsDihedralGroup T) :
    Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ Nonempty (G ≃* PSL2 (ZMod p)) := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  have hcard : Nat.card T = 2 * n :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have heven : Even (Nat.card G) := even_iff_two_dvd.mpr
    (dvd_trans (by rw [hcard]; exact dvd_mul_right 2 n) T.card_subgroup_dvd_card)
  have hnotcyc : ¬ IsCyclic T := by
    intro hc
    exact (Nat.not_even_iff_odd.mpr
      (odd_card_of_cyclic_sylow_two_of_no_normal_index_two T hc (fun N _ => hno N))) heven
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hndvd : n ∣ 2 ^ k := by rw [← hk, hcard]; exact dvd_mul_left n 2
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  have hmpos : 1 ≤ m := by
    by_contra hm0
    have hn : n = 1 := by simpa [show m = 0 by omega] using hm
    exact hnotcyc (e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr hn))
  subst n
  obtain ⟨R, hR, hidx, z, hz, hzc, hout⟩ := dihedral_rotation_data hmpos e
  let : IsCyclic R := hR
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hc := centralizer_eq_sylow_of_rotation_data T hE R hidx z hz hzc hout
  have hclass := T.involutions_conjugate_of_cyclic_index_two R hidx (fun N _ => hno N) z hz
  let localData : DihedralInvolutionCentralizerHypotheses G (m+1) := {
    two_le := by omega
    z := z
    involution := ⟨fun he => by simp [he] at hzG, by simpa only [hzG] using pow_orderOf_eq_one (z : G)⟩
    involutions_conjugate := fun u hu => isConj_iff.mp (hclass u (orderOf_eq_prime hu.2 hu.1))
    centralizer_equiv := ⟨(MulEquiv.subgroupCongr hc).trans (by simpa using e)⟩ }
  rcases localData.recognition with ⟨_, h | h⟩ | ⟨_, h | h⟩ | ⟨_, p, hp, he⟩
  · obtain ⟨eG⟩ := h
    exact Or.inr ⟨3, ⟨by decide, Or.inl ⟨0, rfl⟩⟩,
      ⟨eG.trans psl2_three_equiv_alternatingGroup.symm⟩⟩
  · obtain ⟨eG⟩ := h
    exact Or.inr ⟨5, ⟨by decide, Or.inl ⟨1, rfl⟩⟩,
      ⟨eG.trans alternatingGroupFive_equiv_PSL2.some⟩⟩
  · obtain ⟨eG⟩ := h
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact Or.inr ⟨7, ⟨by decide, Or.inr ⟨3, rfl⟩⟩,
      ⟨eG.trans (psl2_equiv_psl3Two_of_card_seven (F := ZMod 7) (by simp)).some.symm⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, he⟩
end CFSG.Quasithin.ChapterI.SmallSylow


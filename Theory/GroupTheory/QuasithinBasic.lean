module

public import Theory.Quasithin
public import Theory.GroupTheory.TwoLocalTransport
public import Mathlib.Order.Preorder.Finite

/-!
# Rank bounds and the two-local form of quasithin

For a finite group, prime rank is bounded by the group order and is monotone
under embeddings. Transport the abelian p-subgroups along the embedding and
use invariance of generator rank under isomorphism. Every two-local subgroup
lies in a maximal one, so the existing numerical definition `e G ≤ 2` is
equivalent to bounding all odd prime ranks of every two-local subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §0.1
and §A.2. These lemmas concern arbitrary finite groups and do not assume any
classification or K-group hypothesis.
-/

public section

namespace Theory.GroupTheory
open scoped IsMulCommutative

theorem rank_le_card {G : Type*} [Group G] [Finite G] : Group.rank G ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨S, hS, _⟩ := Group.rank_spec G
  exact hS.symm.trans_le (by simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ S)

theorem primeRank_bdd {G : Type*} [Group G] [Finite G] (p : ℕ) :
    BddAbove {n : ℕ | ∃ A : Subgroup G, IsPGroup p A ∧ IsMulCommutative A ∧
      ∃ hA : Group.FG A, n ≤ @Group.rank A inferInstance hA} := by
  refine ⟨Nat.card G, ?_⟩
  rintro n ⟨A, _, _, _, hn⟩
  exact hn.trans (rank_le_card.trans (Subgroup.card_le_card_group A))

theorem primeRank_le_card {G : Type*} [Group G] [Finite G] (p : ℕ) :
    primeRank p G ≤ Nat.card G := by
  apply csSup_le'
  rintro n ⟨A, _, _, _, hn⟩
  exact hn.trans (rank_le_card.trans (Subgroup.card_le_card_group A))

theorem primeRank_le_of_injective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (p : ℕ) (f : G →* H) (hf : Function.Injective f) :
    primeRank p G ≤ primeRank p H := by
  apply csSup_le'
  rintro n ⟨A, hp, hc, _, hn⟩
  let := hc
  let B := A.map f
  have hB : IsMulCommutative B := Subgroup.map_isMulCommutative A f
  have he : Group.rank A = Group.rank B :=
    Group.rank_congr (Subgroup.equivMapOfInjective A f hf)
  exact le_csSup (primeRank_bdd p)
    ⟨B, hp.map f, hB, inferInstance, hn.trans_eq he⟩

theorem primeRank_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (p : ℕ) (f : G ≃* H) :
    primeRank p G = primeRank p H :=
  le_antisymm (primeRank_le_of_injective p f.toMonoidHom f.injective)
    (primeRank_le_of_injective p f.symm.toMonoidHom f.symm.injective)

theorem isQuasithin_iff_maximalTwoLocal {G : Type*} [Group G] [Finite G] :
    IsQuasithin G ↔ ∀ M : Subgroup G, IsMaximalTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2 := by
  have hb : BddAbove {n : ℕ | ∃ M : Subgroup G, M ∈ calM G ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ n ≤ primeRank p M} := by
    refine ⟨Nat.card G, ?_⟩
    rintro n ⟨M, _, p, _, _, hn⟩
    exact hn.trans ((primeRank_le_card p).trans (Subgroup.card_le_card_group M))
  constructor
  · intro h M hM p hp ho
    exact (le_csSup hb ⟨M, hM, p, hp, ho, le_rfl⟩).trans h
  · intro h
    apply csSup_le'
    rintro n ⟨M, hM, p, hp, ho, hn⟩
    exact hn.trans (h M hM p hp ho)

theorem isQuasithin_iff_twoLocal {G : Type*} [Group G] [Finite G] :
    IsQuasithin G ↔ ∀ M : Subgroup G, IsTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p M ≤ 2 := by
  rw [isQuasithin_iff_maximalTwoLocal]
  constructor
  · intro h M hM
    obtain ⟨N, hMN, hN⟩ := Finite.exists_le_maximal hM
    intro p hp ho
    exact (primeRank_le_of_injective p (Subgroup.inclusion hMN)
      (Subgroup.inclusion_injective hMN)).trans (h N hN p hp ho)
  · intro h M hM
    exact h M hM.1
theorem isMaximalTwoLocal_map {G H : Type*} [Group G] [Group H]
    (f : G ≃* H) {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    IsMaximalTwoLocal (M.map f.toMonoidHom) := by
  refine ⟨isTwoLocal_map f hM.1, ?_⟩
  intro N hN hMN
  have hle : M ≤ N.map f.symm.toMonoidHom := by
    simpa [Subgroup.map_map] using Subgroup.map_mono (f := f.symm.toMonoidHom) hMN
  have hn := hM.2 (isTwoLocal_map f.symm hN) hle
  simpa [Subgroup.map_map] using Subgroup.map_mono (f := f.toMonoidHom) hn

theorem isQuasithin_of_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G ≃* H) (h : IsQuasithin G) : IsQuasithin H := by
  rw [isQuasithin_iff_twoLocal] at h ⊢
  intro M hM p hp ho
  have hm := h (M.map f.symm.toMonoidHom) (isTwoLocal_map f.symm hM) p hp ho
  rwa [← primeRank_equiv p (Subgroup.equivMapOfInjective M
    f.symm.toMonoidHom f.symm.injective)] at hm
end Theory.GroupTheory

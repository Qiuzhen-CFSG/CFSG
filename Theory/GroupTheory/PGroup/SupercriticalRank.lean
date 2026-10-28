module

public import Theory.GroupTheory.PGroup.Supercritical
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Prime rank detected by a supercritical subgroup

If a supercritical subgroup X of a finite odd p-group has p-rank at most
one, it is cyclic and its exponent bound gives |X| ≤ p. A nontrivial normal
subgroup of order p is central. Thus every order-p element of the ambient
group lies in X, which bounds its elementary abelian subgroups by p.
The elementary-rank characterization retains the existing abelian-generator
meaning of `primeRank`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.21(4), printed pp.24–25.
-/

open Subgroup
namespace IsSupercriticalPSubgroup
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

/-- Rank at most one in the supercritical subgroup bounds ambient p-rank. -/
public theorem primeRank_le_one_of_rank_le_one (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) (hr : primeRank p X ≤ 1) :
    primeRank p P ≤ 1 := by
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsCyclic X := (hP.to_subgroup X).isCyclic_of_odd_of_elementary_card_le hp
    (fun E hE => by
      let : IsElementaryAbelian p E := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  have hcard : Nat.card X ≤ p := by
    apply Nat.le_of_dvd (Fact.out : p.Prime).pos
    rw [← IsCyclic.exponent_eq_card]
    exact hX.exponent_dvd_p
  have hcentral : X ≤ center P := by
    cases subsingleton_or_nontrivial X with
    | inl h =>
      let := h
      intro x hx
      have he : (⟨x, hx⟩ : X) = 1 := Subsingleton.elim _ _
      have he' : x = 1 := congrArg Subtype.val he
      exact he' ▸ (center P).one_mem
    | inr h =>
      obtain ⟨Z, _, hZX, hZ, hZc⟩ :=
        exists_central_subgroup_card_eq_prime_in_normal (p := p) X h
      have he : Z = X := eq_of_le_of_card_ge hZX (by omega)
      exact he ▸ hZc
  apply primeRank_le_of_pow_eq_one_subset X (by simpa using hcard)
  intro x hx
  by_cases he : x = 1
  · exact he ▸ X.one_mem
  · apply hX.order_p_mem x
    · intro y hy
      exact ((mem_center_iff.mp (hcentral hy)) x).symm
    · exact orderOf_eq_prime_iff.mpr ⟨hx, he⟩

/-- A supercritical subgroup detects ambient p-rank greater than one. -/
public theorem one_lt_primeRank (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) (hr : 1 < primeRank p P) :
    1 < primeRank p X := by
  by_contra hn
  exact (not_le_of_gt hr) (hX.primeRank_le_one_of_rank_le_one hP hp (by omega))
end IsSupercriticalPSubgroup

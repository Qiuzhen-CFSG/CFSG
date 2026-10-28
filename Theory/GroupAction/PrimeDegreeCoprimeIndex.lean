module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

/-!
# Transitivity retained by a subgroup of coprime index

Let a finite group K act transitively on a finite set of prime cardinal p.
Any subgroup H whose index is coprime to p is transitive for the literal
restricted action on the same set. No normality of H or equality of its
index with a chosen orbit size is required.

For a point x, the full stabilizer L has index p. The inclusion H∩L≤L
and the index tower show that p divides |H:H∩L|·|K:H|. Coprimality makes
p divide the H-orbit cardinal. That cardinal is positive and at most p,
so the orbit is the whole set. The proof preserves the supplied action
and derives the restricted stabilizer through the native subgroup action.

This prime-degree transfer is used for the three neighboring vertices in
Stellmacher (10.1), source (16), printed p.64, after selecting a point in
the actual affine four-element coset with stabilizer index prime to three.
-/

namespace MulAction

public theorem isPretransitive_of_prime_card_of_coprime_index
    {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    [IsPretransitive K X] {p : ℕ} (_hprime : p.Prime)
    (hcard : Nat.card X=p) (H : Subgroup K) (hcop : Nat.Coprime p H.index) :
    IsPretransitive H X := by
  classical
  constructor
  intro x y
  let L := stabilizer K x
  have hindex : L.index=p := (index_stabilizer_of_transitive K x).trans hcard
  have hdvd : p∣(H⊓L).index := hindex ▸ Subgroup.index_dvd_of_le (show H⊓L≤L from inf_le_right)
  rw [←Subgroup.relIndex_mul_index (show H⊓L≤H from inf_le_left),
    Subgroup.inf_relIndex_left] at hdvd
  have horbitDvd : p∣(orbit H x).ncard := by
    have hh := hcop.dvd_of_dvd_mul_right hdvd
    change p∣(stabilizer H x).index at hh
    rwa [index_stabilizer] at hh
  have hpos : 0<(orbit H x).ncard := (Set.ncard_pos).mpr ⟨x,mem_orbit_self x⟩
  have hbound : (orbit H x).ncard≤p := hcard ▸ Set.ncard_le_card _
  have heq : (orbit H x).ncard=Nat.card X := by
    rw [hcard]
    exact le_antisymm hbound (Nat.le_of_dvd hpos horbitDvd)
  have hfull : orbit H x=Set.univ := (Set.eq_univ_iff_ncard _).mpr heq
  have hy : y∈orbit H x := hfull ▸ Set.mem_univ y
  exact hy

end MulAction

module
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Fixed-normalized subgroups in invariant Hall subgroups

Under a coprime action on a finite solvable group, every invariant pi-subgroup
normalized by the full fixed subgroup lies in each invariant Hall pi-subgroup.
The supplied action is retained, and the prime set is arbitrary.

Extend the invariant pi-subgroup to an invariant Hall subgroup. Fixed-point
Hall conjugacy compares that subgroup with the prescribed Hall subgroup by
a fixed conjugator. The conjugator normalizes the original pi-subgroup, so
conjugating its containment gives the claimed inclusion.

This is the containment underlying Kurzweil–Stellmacher, *The Theory of
Finite Groups*, §8.2.6(d), printed p.187. It provides the common Hall bound
in the signalizer truncation construction of §11.1.6.
-/

public theorem le_invariant_hall_of_fixed_normalized
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set Nat.Primes} {P U : Subgroup G}
    (hP : IsHallSubgroup π P) (hPI : IsInvariant A G P)
    (hU : IsPiSubgroup π U) (hUI : IsInvariant A G U)
    (hUN : FixedPoints.subgroup A G ≤ Subgroup.normalizer (U : Set G)) : U ≤ P := by
  obtain ⟨Q, hQ, hQI, hUQ⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup hsolv hcop π U hU hUI
  obtain ⟨c, hc, hPQ⟩ :=
    exists_fixedPoint_conj_of_isHallSubgroup_of_isInvariant hsolv hcop π hP hQ hPI hQI
  intro x hx
  have hconj : MulAut.conj c x ∈ U := (Subgroup.mem_normalizer_iff.mp (hUN hc) x).mp hx
  have hxQ := hUQ hconj
  rw [hPQ] at hxQ
  obtain ⟨y, hy, hyx⟩ := hxQ
  rwa [(MulAut.conj c).injective hyx] at hy

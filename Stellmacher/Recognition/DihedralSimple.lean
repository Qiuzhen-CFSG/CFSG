module

public import Stellmacher.MainDefs
public import GorensteinWalter.FinalTheorem
public import GorensteinWalter.SimpleDGroup
public import Theory.GroupTheory.CyclicSylowTwoOddOrder

/-!
# Simple-group recognition in the dihedral Sylow branch

A finite nonsolvable simple group with the supplied dihedral Sylow
two-subgroup is isomorphic to `A₇` or to `PSL₂(K)` for an odd finite field.
The conclusion uses the actual group models, and the hypothesis keeps
Stellmacher's polygonal-dihedral definition with its unrestricted parameter.

The Sylow cardinality forces that parameter to be a power of two. The
order-two case is cyclic, so Burnside transfer would give a normal subgroup
of index two, impossible in a nonsolvable simple group. Sylow equivalences
then give the exact dihedral hypothesis of the proved Gorenstein–Walter
theorem. Its D-group conclusion is eliminated by `simple_dgroup_recognition`,
which removes the odd core and the two-group and PGL₂ alternatives.

Source: the dihedral branch of Stellmacher's Theorem 2 in
`refs/latex/stellmacher-n-group.tex`, followed by the simple-group corollary
of Gorenstein–Walter as formalized in `GorensteinWalter.FinalTheorem`.
-/

namespace Stellmacher.Recognition

universe u

open scoped IsMulCommutative

private theorem no_normal_index_two
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp [htop] at hi

private theorem even_card_of_dihedral_sylow
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hd : Stellmacher.IsDihedralGroup S) :
    Even (Nat.card G) := by
  obtain ⟨n, ⟨e⟩⟩ := hd
  have hcard : Nat.card S = 2 * n :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  apply even_iff_two_dvd.mpr
  exact dvd_trans (by rw [hcard]; exact dvd_mul_right 2 n)
    S.card_subgroup_dvd_card

private theorem has_dihedral_sylow_two
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (hd : Stellmacher.IsDihedralGroup S) :
    GorensteinWalter.HasDihedralSylowTwo G := by
  have heven := even_card_of_dihedral_sylow S hd
  have hnotcyc : ¬ IsCyclic S := by
    intro hcyc
    exact (Nat.not_even_iff_odd.mpr
      (odd_card_of_cyclic_sylow_two_of_no_normal_index_two
        S hcyc (no_normal_index_two hns))) heven
  obtain ⟨n, ⟨e⟩⟩ := hd
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hcard : Nat.card S = 2 * n :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hndvd : n ∣ 2 ^ k := by rw [← hk, hcard]; exact dvd_mul_left n 2
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  have hmpos : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hn : n = 1 := by simpa [hm0'] using hm
    exact hnotcyc (e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr hn))
  intro T
  refine ⟨m, hmpos, ?_⟩
  subst n
  exact ⟨(Sylow.equiv S T).symm.trans e⟩

/-- A nonsolvable finite simple group with the supplied dihedral Sylow
two-subgroup is an actual alternating-seven or odd-field PSL2 model. -/
public theorem simple_dihedral_recognition
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (S0 : Sylow 2 G) (hd : Stellmacher.IsDihedralGroup S0) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type u) (instK : Field K) (_ : Finite K),
        let : Field K := instK
        Odd (Nat.card K) ∧ Nonempty (G ≃* GorensteinWalter.PSL2 K) := by
  exact GorensteinWalter.simple_dgroup_recognition hns
    (even_card_of_dihedral_sylow S0 hd)
    (GorensteinWalter.gorensteinWalter G (has_dihedral_sylow_two hns S0 hd))

end Stellmacher.Recognition

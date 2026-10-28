module

public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Two-rank bounds for dihedral and semidihedral groups

The cyclic rotation subgroup has index two. The intersection of an
elementary abelian subgroup with it has order at most two, so the index
rank bound gives two-rank at most two.

Source application: Aschbacher–Smith, 16.3.8–9, printed pp.1179–1180.
-/

public section

open Subgroup
namespace Theory.GroupTheory

private theorem cyclic_rank {A : Type*} [Group A] [Finite A] [IsCyclic A] :
    primeRank 2 A ≤ 1 := by
  let P : Sylow 2 A := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic inferInstance

private theorem cyclic_index_two_rank {A : Type*} [Group A] [Finite A]
    (C : Subgroup A) [IsCyclic C] (hC : C.index = 2) : primeRank 2 A ≤ 2 := by
  have hi : C.index ≤ 2 ^ 1 := by simp only [pow_one, hC, le_refl]
  have hr := primeRank_le_add_of_index_le C hi
  have hc := cyclic_rank (A := C)
  omega

/-- Every dihedral two-group has two-rank at most two. -/
theorem dihedral_rank_le_two (n : ℕ) : primeRank 2 (DihedralGroup (2 ^ n)) ≤ 2 := by
  let C := zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ n))
  apply cyclic_index_two_rank C
  have hc : Nat.card C = 2 ^ n := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hi := C.card_mul_index
  rw [hc, DihedralGroup.nat_card] at hi
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  nlinarith

/-- Every standard semidihedral group has two-rank at most two. -/
theorem semidihedral_rank_le_two (n : ℕ) (hn : 4 ≤ n) : primeRank 2 (Semidihedral.StandardModel n hn) ≤ 2 := by
  let f : Multiplicative (ZMod (2 ^ (n - 1))) →* Semidihedral.StandardModel n hn :=
    SemidirectProduct.inl
  let C := f.range
  let : IsCyclic C := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply cyclic_index_two_rank C
  have hc : Nat.card C = 2 ^ (n - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    simp
  have hi := C.card_mul_index
  have he : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
  rw [hc, Semidihedral.standardModel_card, he] at hi
  have hp : 0 < 2 ^ (n - 1) := pow_pos (by decide) _
  nlinarith

end Theory.GroupTheory

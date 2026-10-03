module
public import Theory.GroupTheory.SylowNormalClosure
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral


/-!
# Sylows in quotients of odd dihedral groups

A finite quotient of a dihedral group of order twice an odd number has
Sylow two-subgroups of order at most two, and each such Sylow normally
generates the quotient. This supplies the pure group input in the faithful
quotient bridge from Stellmacher (6.3) to (8.2), printed p.37.

The Sylow order is a power of two dividing 2n; coprimality with odd n makes
it divide two. Every reflection image has square one, hence lies in the
Sylow normal closure by the generic p-subgroup bound. Rotations are products
of two reflections, so surjectivity gives the whole quotient. This argument
uses no action, characteristic-two, or additional quotient-kernel premise.
-/

public theorem odd_dihedral_quotient_sylow
    {G : Type*} [Group G] [Finite G] (n : ℕ) (hn : Odd n)
    (q : DihedralGroup n →* G) (hq : Function.Surjective q)
    (S : Sylow 2 G) :
    Nat.card S ≤ 2 ∧
      Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤ := by
  have hdiv : Nat.card S ∣ 2 * n := by
    rw [← DihedralGroup.nat_card]
    exact (Subgroup.card_subgroup_dvd_card (S : Subgroup G)).trans
      (Subgroup.card_dvd_of_surjective q hq)
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) n := by
    rw [hk]
    exact hn.coprime_two_left.pow_left k
  refine ⟨Nat.le_of_dvd (by decide) (hcop.dvd_of_dvd_mul_right hdiv), ?_⟩
  let N := Subgroup.normalClosure ((S : Subgroup G) : Set G)
  have href (i : ZMod n) : q (DihedralGroup.sr i) ∈ N := by
    have hsq : q (DihedralGroup.sr i) ^ 2 = 1 := by
      rw [← map_pow]
      simp [sq]
    have hp := (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hsq).isPGroup 2 _
    exact hp.le_normalClosure_sylow S (Subgroup.mem_zpowers _)
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := hq x
  cases a with
  | sr i => exact href i
  | r i =>
    have heq : DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i := by simp
    rw [heq, map_mul]
    exact N.mul_mem (href 0) (href i)

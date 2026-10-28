module
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Two-cores in groups acting on three letters

A two-subgroup of S₃ has order at most two. If an action on three letters
contains a cubic, its two-core acts trivially: a nontrivial normal image
would be a central involution commuting with the cubic, which S₃ excludes.
This is the kernel calculation used in the nondegenerate-plane centralizer
of Aschbacher--Smith 13.3.12, printed p.889.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem twoSubgroup_card_le_two_permThree
    (P : Subgroup (Equiv.Perm (Fin 3))) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have hd : Nat.card P ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      Nat.factorial_succ, Nat.factorial_zero] using P.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact Nat.le_of_dvd (by decide : 0 < 2) (hcop.dvd_mul_right.mp hd)

private theorem permThree_cubic_commuting_square
    (x y : Equiv.Perm (Fin 3)) (hx : x ^ 3 = 1) (hne : x ≠ 1)
    (hy : y ^ 2 = 1) (hc : Commute x y) : y = 1 := by
  have hh : ∀ x y : Equiv.Perm (Fin 3),
      (x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ x * y = y * x) → y = 1 := by
    decide +kernel
  exact hh x y ⟨hx, hne, hy, hc⟩

theorem twoCore_le_ker_of_permThree_cubic
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (x : G) (hx : orderOf (f x) = 3) :
    pCore 2 G ≤ f.ker := by
  let P := (pCore 2 G).map f.rangeRestrict
  let : P.Normal := (inferInstance : (pCore 2 G).Normal).map
    f.rangeRestrict f.rangeRestrict_surjective
  have hp : IsPGroup 2 P := pCore_isPGroup.map _
  have hd : Nat.card P ∣ 6 := by
    have hh := P.card_subgroup_dvd_card.trans f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      Nat.factorial_succ, Nat.factorial_zero] using hh
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card P ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · have hbot : P = ⊥ := Subgroup.card_eq_one.mp h1
    intro g hg
    have hmem : f.rangeRestrict g ∈ P := mem_map_of_mem _ hg
    have he : f.rangeRestrict g = 1 := by
      simpa only [hbot, mem_bot] using hmem
    exact congrArg Subtype.val he
  · have hc := central_of_normal_card_two P h2
    intro g hg
    let y : P := ⟨f.rangeRestrict g, mem_map_of_mem _ hg⟩
    have hy : f g ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := y)
      rw [h2] at hh
      exact congrArg (fun z : P => (z.val : Equiv.Perm (Fin 3))) hh
    apply permThree_cubic_commuting_square (f x) (f g)
    · simpa only [hx] using pow_orderOf_eq_one (f x)
    · intro he
      rw [he, orderOf_one] at hx
      omega
    · exact hy
    · exact congrArg Subtype.val ((mem_center_iff.mp (hc y.property)) (f.rangeRestrict x))

end Theory.GroupTheory

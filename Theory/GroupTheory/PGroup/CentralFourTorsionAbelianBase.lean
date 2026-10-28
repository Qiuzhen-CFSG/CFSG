module

public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Theory.GroupTheory.PGroup.NormalAbelian

/-!
# A rank-two abelian base for groups with central fourth roots

A maximal normal abelian subgroup containing the center is self-centralizing.
If all fourth roots of one are central, it contains every square root of one.
An exact count of four square roots therefore gives two nontrivial cyclic
factors by the finite abelian structure theorem. Conjugation fixes the fourth
roots in this base.

This is an abelian-base reduction for the structural argument cited in
MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*,
Trans. AMS 150 (1970), printed p.377, assertion (xvii). It does not use the
metacyclicity conclusion cited there from Alperin (J. Algebra 1 (1964)).
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup

/-- A central fourth-root condition and four square roots give a normal
self-centralizing abelian base with two nontrivial cyclic factors. -/
public theorem exists_rank_two_abelian_base_of_central_fourth_roots
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (hfour : ∀ x : Q, x ^ 4 = 1 → x ∈ center Q)
    (hcount : Nat.card {x : Q // x ^ 2 = 1} = 4) :
    ∃ A : Subgroup Q, A.Normal ∧ IsMulCommutative A ∧
      center Q ≤ A ∧ centralizer (A : Set Q) ≤ A ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
        (A ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  obtain ⟨A, hZA, hAn, hAc, _, hCA⟩ :=
    exists_normal_abelian_selfCentralizing_containing hQ (center Q)
      inferInstance inferInstance
  let : IsMulCommutative A := hAc
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hall (x : Q) (hx : x ^ 2 = 1) : x ∈ A := by
    apply hZA (hfour x ?_)
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx, one_pow]
  let e : {x : Q // x ^ 2 = 1} ≃ {x : A // x ^ 2 = 1} :=
    { toFun x := ⟨⟨x, hall x x.property⟩, Subtype.ext x.property⟩
      invFun x := ⟨x.val, congrArg Subtype.val x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcountA : Nat.card (omega₁ A (p := 2)) = 4 := by
    rw [← square_ker_eq_omega_one]
    exact (Nat.card_congr e).symm.trans hcount
  exact ⟨A, hAn, hAc, hZA, hCA,
    (hQ.to_subgroup A).equiv_two_cyclic_factors_of_card_omega_one_eq_four hcountA⟩

/-- Conjugation fixes the fourth roots in any normal subgroup when all ambient
fourth roots are central. -/
public theorem conjNormal_fixed_of_central_fourth_roots
    {Q : Type*} [Group Q]
    (hfour : ∀ x : Q, x ^ 4 = 1 → x ∈ center Q)
    (A : Subgroup Q) [A.Normal] (g : Q) (a : A) (ha : a ^ 4 = 1) :
    MulAut.conjNormal (H := A) g a = a := by
  apply Subtype.ext
  change g * (a : Q) * g⁻¹ = a
  rw [mem_center_iff.mp (hfour a (congrArg Subtype.val ha)) g, mul_inv_cancel_right]

end IsPGroup

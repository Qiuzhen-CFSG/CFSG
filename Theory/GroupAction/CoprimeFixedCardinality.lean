module

public import Theory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# Fixed-point cardinality under coprime quotient actions

For a coprime action on a finite solvable group, the order of the fixed
subgroup is the product of the fixed quotient order and the order of the
fixed part of the kernel. This follows by restricting the quotient map
to fixed points and applying coprime fixed-point lifting.

For a subgroup A of an actor H, a bound m |C_{K/N}(H)| ≤ |C_{K/N}(A)|
therefore lifts to m |C_K(H)| ≤ |C_K(A)|: the H-fixed part of the kernel
is contained in its A-fixed part. A nonidentity H-fixed element supplies
the useful lower bound 2m. These are cardinal consequences of the coprime
fixed-point theorem proved in `Theory.GroupAction.Quotient`.
-/

namespace FixedPoints

/-- Coprime fixed-point lifting gives the kernel/image product formula. -/
public theorem card_eq_quotient_mul_kernel_of_coprime
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K]
    (hsolv : Group.IsSolvable K) (hcop : Nat.Coprime (Nat.card A) (Nat.card K))
    (N : Subgroup K) [N.Normal] (hN : IsInvariant A K N) :
    letI : MulDistribMulAction A (K ⧸ N) := quotientMulDistribMulAction N hN
    Nat.card (subgroup A K) =
      Nat.card (subgroup A (K ⧸ N)) * Nat.card ↥(N ⊓ subgroup A K) := by
  let : MulDistribMulAction A (K ⧸ N) := quotientMulDistribMulAction N hN
  let C := subgroup A K
  let f := (QuotientGroup.mk' N).comp C.subtype
  have hrange : f.range = subgroup A (K ⧸ N) := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop N hN]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.property, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  let e : f.ker ≃ ↥(N ⊓ C) :=
    { toFun := fun x => ⟨x.val.val,
        (QuotientGroup.eq_one_iff x.val.val).mp x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.2⟩,
        (QuotientGroup.eq_one_iff x.val).mpr x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card C = Nat.card f.range * Nat.card f.ker := by
      rw [← Subgroup.index_ker, Subgroup.index_mul_card]
    _ = _ := by rw [hrange, Nat.card_congr e]

/-- A lower bound relative to all fixed points lifts through an invariant quotient. -/
public theorem mul_card_le_of_quotient
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    [MulDistribMulAction H K]
    (hsolv : Group.IsSolvable K) (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (A : Subgroup H) (N : Subgroup K) [N.Normal] (hN : IsInvariant H K N)
    (m : ℕ) :
    letI : MulDistribMulAction H (K ⧸ N) := quotientMulDistribMulAction N hN
    m * Nat.card (subgroup H (K ⧸ N)) ≤ Nat.card (subgroup A (K ⧸ N)) →
      m * Nat.card (subgroup H K) ≤ Nat.card (subgroup A K) := by
  let : MulDistribMulAction H (K ⧸ N) := quotientMulDistribMulAction N hN
  intro hbound
  have hNA : IsInvariant A K N := ⟨fun a x => hN.invariant a.val x⟩
  have hcopA := hcop.of_dvd_left A.card_subgroup_dvd_card
  have hH := card_eq_quotient_mul_kernel_of_coprime hsolv hcop N hN
  have hA := card_eq_quotient_mul_kernel_of_coprime hsolv hcopA N hNA
  have hle : N ⊓ subgroup H K ≤ N ⊓ subgroup A K := by
    intro x hx
    exact ⟨hx.1, fun a => hx.2 a.val⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [hH, hA, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hbound hcard

/-- A nonidentity common fixed point doubles the lifted fixed-point ratio bound. -/
public theorem two_mul_le_card_of_quotient_ratio
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    [MulDistribMulAction H K]
    (hsolv : Group.IsSolvable K) (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (A : Subgroup H) (N : Subgroup K) [N.Normal] (hN : IsInvariant H K N)
    (m : ℕ) (y : K) (hy : y ≠ 1) (hfix : ∀ h : H, h • y = y) :
    letI : MulDistribMulAction H (K ⧸ N) := quotientMulDistribMulAction N hN
    m * Nat.card (subgroup H (K ⧸ N)) ≤ Nat.card (subgroup A (K ⧸ N)) →
      2 * m ≤ Nat.card (subgroup A K) := by
  let : MulDistribMulAction H (K ⧸ N) := quotientMulDistribMulAction N hN
  intro hbound
  have hne : subgroup H K ≠ ⊥ := by
    intro heq
    have hm : y ∈ subgroup H K := hfix
    rw [heq, Subgroup.mem_bot] at hm
    exact hy hm
  have htwo : 2 ≤ Nat.card (subgroup H K) :=
    (subgroup H K).one_lt_card_iff_ne_bot.mpr hne
  have h := mul_card_le_of_quotient hsolv hcop A N hN m hbound
  calc
    2 * m = m * 2 := Nat.mul_comm _ _
    _ ≤ m * Nat.card (subgroup H K) := Nat.mul_le_mul_left m htwo
    _ ≤ _ := h

end FixedPoints

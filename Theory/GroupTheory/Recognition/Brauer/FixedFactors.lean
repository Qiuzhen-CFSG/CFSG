module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData
public import Theory.GroupTheory.FixedInvertedFactorization
public import Theory.GroupTheory.Recognition.Brauer.InvertedSubgroups
public import Theory.GroupTheory.Recognition.Brauer.FixedFactorOrders
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The fixed factors in Brauer's involution geometry

For the original first three postulates of Brauer I, the subgroups `M` and
`Mstar` are internal direct products of their centralizers of `j1` and `j2`.
All four factors have the same odd order `q`, and both parent subgroups have
order `q²`. These are equations (2.4)–(2.5) of Richard Brauer, *On finite
Desarguesian planes I*, Math. Z. 90 (1965), pp. 118–119. They provide the
algebraic decomposition used by the subsequent incidence and counting proofs.

Conjugation by `j` makes the parent subgroups abelian of odd order, by
`inverted_subgroups`. Conjugation by `j1` is involutive, so the unique
fixed/inverted factorization gives an internal complement. Since `j` inverts
the subgroup, the inverted factor is precisely the centralizer of `j*j1`.
Postulate (III), via `fixed_factor_card_eq`, equates the factor orders;
equal parent orders then identify the starred factor order with `q`.
-/

namespace Theory.GroupTheory

private theorem fixed_complement
    {G : Type*} [Group G] (H : Subgroup G) [Finite H] (j j1 : G)
    (hj1 : orderOf j1 = 2) (hn1 : j1 ∈ Subgroup.normalizer (H : Set G))
    (hc : ∀ a b : H, Commute a b) (ho : Odd (Nat.card H))
    (hi : ∀ m : H, j * (m : G) * j⁻¹ = (m : G)⁻¹) :
    ((H ⊓ Subgroup.centralizer ({j1} : Set G)).subgroupOf H).IsComplement'
      ((H ⊓ Subgroup.centralizer ({j * j1} : Set G)).subgroupOf H) := by
  let A : Subgroup H := (H ⊓ Subgroup.centralizer ({j1} : Set G)).subgroupOf H
  let B : Subgroup H := (H ⊓ Subgroup.centralizer ({j * j1} : Set G)).subgroupOf H
  let φ : MulAut H := H.normalizerMonoidHom ⟨j1, hn1⟩
  have hsq : j1 * j1 = 1 := by simpa only [hj1, pow_two] using pow_orderOf_eq_one j1
  have hInv : j1⁻¹ = j1 := inv_eq_iff_mul_eq_one.mpr hsq
  have hφ : Function.Involutive φ := by
    intro m
    apply Subtype.ext
    change j1 * (j1 * (m : G) * j1⁻¹) * j1⁻¹ = (m : G)
    simp only [hInv, mul_assoc, hsq, mul_one]
    rw [← mul_assoc, hsq, one_mul]
  have hA (m : H) : φ m = m ↔ m ∈ A := by
    constructor
    · intro hm
      have heq : j1 * (m : G) * j1⁻¹ = (m : G) := congrArg Subtype.val hm
      change (m : G) ∈ H ⊓ Subgroup.centralizer ({j1} : Set G)
      exact ⟨m.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp heq).symm⟩
    · intro hm
      change (m : G) ∈ H ⊓ Subgroup.centralizer ({j1} : Set G) at hm
      apply Subtype.ext
      change j1 * (m : G) * j1⁻¹ = (m : G)
      exact mul_inv_eq_iff_eq_mul.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hm.2).symm
  have hB (m : H) : φ m = m⁻¹ ↔ m ∈ B := by
    have heval : (j * j1) * (m : G) * (j * j1)⁻¹ = ((φ m : H) : G)⁻¹ := by
      calc
        (j * j1) * (m : G) * (j * j1)⁻¹ =
            j * (j1 * (m : G) * j1⁻¹) * j⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
        _ = ((φ m : H) : G)⁻¹ := hi (φ m)
    constructor
    · intro hm
      change (m : G) ∈ H ⊓ Subgroup.centralizer ({j * j1} : Set G)
      refine ⟨m.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have heq : (j * j1) * (m : G) * (j * j1)⁻¹ = (m : G) := by
        rw [heval, hm]
        simp
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    · intro hm
      change (m : G) ∈ H ⊓ Subgroup.centralizer ({j * j1} : Set G) at hm
      have heq : (j * j1) * (m : G) * (j * j1)⁻¹ = (m : G) :=
        mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hm.2).symm
      rw [heval] at heq
      apply Subtype.ext
      change ((φ m : H) : G) = (m : G)⁻¹
      exact inv_eq_iff_eq_inv.mp heq
  change A.IsComplement' B
  apply Subgroup.isComplement_iff_existsUnique.mpr
  intro x
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, hu⟩ := existsUnique_fixed_inverted_mul hc ho φ hφ x
  refine ⟨(⟨a, (hA a).mp ha⟩, ⟨b, (hB b).mp hb⟩), hab, ?_⟩
  rintro ⟨a', b'⟩ hprod
  have heq : ((a' : H), (b' : H)) = (a, b) :=
    hu _ ⟨(hA a').mpr a'.property, (hB b').mpr b'.property, hprod⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
    (Subtype.ext (congrArg Prod.snd heq))

namespace BrauerPlaneSeed

/-- Brauer I (2.4)–(2.5): complementary commuting factors of common odd order. -/
public theorem fixed_factors {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    (S.M1.subgroupOf S.M).IsComplement' (S.M2.subgroupOf S.M) ∧
    (S.Mstar1.subgroupOf S.Mstar).IsComplement' (S.Mstar2.subgroupOf S.Mstar) ∧
    (∀ a b : S.M, Commute a b) ∧ (∀ a b : S.Mstar, Commute a b) ∧
    Odd S.q ∧ Nat.card S.M2 = S.q ∧ Nat.card S.Mstar1 = S.q ∧
    Nat.card S.Mstar2 = S.q ∧ Nat.card S.M = S.q ^ 2 ∧ Nat.card S.Mstar = S.q ^ 2 := by
  obtain ⟨hMprops, hSprops⟩ := S.inverted_subgroups
  have hpairs := S.fixed_factor_card_eq
  obtain ⟨hMo, hMc, hMi⟩ := hMprops
  obtain ⟨hSo, hSc, hSi⟩ := hSprops
  have hjj : S.j * S.j = 1 := by simpa only [S.j_order, pow_two] using pow_orderOf_eq_one S.j
  have hji : S.j⁻¹ = S.j := inv_eq_iff_mul_eq_one.mpr hjj
  have hj1C : S.j1 ∈ Subgroup.centralizer ({S.j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr S.j_commute_j1.symm.eq
  have hMcomp := fixed_complement S.M S.j S.j1 S.j1_order
    (S.centralizer_le_normalizer_M hj1C) hMc hMo
    (fun m => by simpa only [hji] using hMi m)
  have hScomp := fixed_complement S.Mstar S.j S.j1 S.j1_order
    (S.centralizer_le_normalizer_Mstar hj1C) hSc hSo
    (fun m => by simpa only [hji] using hSi m)
  change (S.M1.subgroupOf S.M).IsComplement' (S.M2.subgroupOf S.M) at hMcomp
  change (S.Mstar1.subgroupOf S.Mstar).IsComplement' (S.Mstar2.subgroupOf S.Mstar) at hScomp
  have hMcard : Nat.card S.M1 * Nat.card S.M2 = Nat.card S.M := by
    have h1 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := S.M1) (K := S.M) inf_le_left).toEquiv
    have h2 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := S.M2) (K := S.M) inf_le_left).toEquiv
    simpa only [h1, h2] using hMcomp.card_mul_card
  have hScard : Nat.card S.Mstar1 * Nat.card S.Mstar2 = Nat.card S.Mstar := by
    have h1 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := S.Mstar1) (K := S.Mstar) inf_le_left).toEquiv
    have h2 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := S.Mstar2) (K := S.Mstar) inf_le_left).toEquiv
    simpa only [h1, h2] using hScomp.card_mul_card
  have hMsize : Nat.card S.M = S.q ^ 2 := by
    rw [← hMcard, ← hpairs.1]
    simp only [BrauerPlaneSeed.q, pow_two]
  have hSsize : Nat.card S.Mstar = S.q ^ 2 := S.card_M_eq_Mstar.symm.trans hMsize
  have hSq : Nat.card S.Mstar1 = S.q := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    rw [← hpairs.2] at hScard
    simpa only [pow_two] using hScard.trans hSsize
  have hqodd : Odd S.q := by
    rw [hMsize] at hMo
    exact (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp hMo
  exact ⟨hMcomp, hScomp, hMc, hSc, hqodd, hpairs.1.symm,
    hSq, hpairs.2.symm.trans hSq, hMsize, hSsize⟩

end BrauerPlaneSeed
end Theory.GroupTheory

module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.PrimeProduct.Structure
/-!
# Nonabelian normal subgroups in the prime-product row

The two-residual has index two: four divides its PSL₂ factor, the ambient
Sylow has order eight, and the specified outer element is outside the
residual. An element centralizing PSL₂ cannot lie in the other coset,
since that would make the specified outer automorphism inner. Inside the
residual, the centralizer is contained in the cubic factor.

Simplicity now shows that every nonabelian normal subgroup contains the
actual PSL₂ factor. This applies to the terminal Thompson image without
identifying it with the ambient quotient or the offender actor.

Source: Aschbacher–Smith, F.6.17–18, printed pp.309–310, and the terminal
comparison of F.6.18 with B.5.6 on printed p.1155.
-/

public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace LowRows.PrimeProduct
variable {D : Type*} [Group D] [Finite D] {S : Sylow 2 D} (c : FSource.ProductRow S)
include c

/-- The source residual has exactly two cosets in the actual ambient group. -/
theorem residual_index (hS : Nat.card S = 8) : (pResidual 2 D).index = 2 := by
  obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := D) 2).exists_card_eq
  have hi : (pResidual 2 D).index = 2 ^ n := hn
  have hr : 4 ∣ Nat.card (pResidual 2 D) := by
    rw [c.residual, ← Nat.card_congr c.product.toEquiv, Nat.card_prod]
    exact dvd_mul_of_dvd_left (four_dvd_first_card c) _
  have hd : 2 ^ (n + 2) ∣ Nat.card D := by
    rw [← (pResidual 2 D).index_mul_card, hi, pow_add]
    exact mul_dvd_mul_left _ hr
  have hb := Nat.le_of_dvd (Nat.card_pos (α := S)) (S.pow_dvd_card_of_pow_dvd_card hd)
  rw [hS] at hb
  have hl : n + 2 ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hne : (pResidual 2 D).index ≠ 1 := by
    intro h
    exact outer_element_not_mem_residual c (index_eq_one.mp h ▸ mem_top _)
  have hpos : n ≠ 0 := by intro h; apply hne; rw [hi, h]; rfl
  have he : n = 1 := by omega
  simp [hi, he]

omit [Finite D] in
private theorem not_inner_outer_product {t : D}
    (h : FFAlternatives.InducesOuter c.first t)
    (a : c.first) (x : D) (hx : x ∈ centralizer (c.first : Set D))
    (ht : t = (a : D) * x) : False := by
  obtain ⟨α,hα,hout⟩ := h
  apply hout
  refine ⟨a, ?_⟩
  ext k
  change (a : D) * k * (a : D)⁻¹ = (α k : D)
  rw [hα, ht]
  calc
    (a : D) * k * (a : D)⁻¹ = (a : D) * ((k : D) * x) * x⁻¹ * (a : D)⁻¹ := by group
    _ = (a : D) * (x * k) * x⁻¹ * (a : D)⁻¹ := by rw [mem_centralizer_iff.mp hx k k.property]
    _ = ((a : D) * x) * k * ((a : D) * x)⁻¹ := by group

/-- The outer coset has no element centralizing the first factor. -/
theorem first_centralizer_le_residual (hS : Nat.card S = 8) :
    centralizer (c.first : Set D) ≤ pResidual 2 D := by
  intro x hx
  by_contra hnot
  have he : c.element * x⁻¹ ∈ pResidual 2 D :=
    (mul_mem_iff_of_index_two (residual_index c hS)).mpr
      (iff_of_false (outer_element_not_mem_residual c) (by simpa using hnot))
  obtain ⟨⟨a,b⟩,hab⟩ := c.product.surjective ⟨c.element * x⁻¹, c.residual ▸ he⟩
  have hab' : (a : D) * b = c.element * x⁻¹ :=
    (c.product_apply a b).symm.trans (congrArg Subtype.val hab)
  have hb : (b : D) ∈ centralizer (c.first : Set D) := by
    intro k hk
    exact first_commutes_second c ⟨k,hk⟩ b
  exact not_inner_outer_product c c.firstOuter a ((b : D) * x)
    (mul_mem hb hx) (by rw [← mul_assoc, hab']; group)

omit [Finite D] in
/-- The simple perfect first factor has trivial center. -/
theorem first_center : center c.first = ⊥ := by
  let : IsSimpleGroup c.first := first_simple c
  let : Group.IsPerfect c.first := first_perfect c
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center c.first) inferInstance with h | h
  · exact h
  · have hc : IsMulCommutative c.first := center_eq_top_iff.mp h
    have hb : (⊤ : Subgroup c.first) = ⊥ :=
      Group.IsPerfect.commutator_eq_top.symm.trans ((commutator_eq_bot_iff _).mpr hc)
    exact (top_ne_bot hb).elim

/-- Its ambient centralizer lies in the actual abelian cubic factor. -/
theorem first_centralizer_le_second (hS : Nat.card S = 8) :
    centralizer (c.first : Set D) ≤ c.second := by
  intro x hx
  have hr := first_centralizer_le_residual c hS hx
  obtain ⟨⟨a,b⟩,hab⟩ := c.product.surjective ⟨x,c.residual ▸ hr⟩
  have hab' : (a : D) * b = x :=
    (c.product_apply a b).symm.trans (congrArg Subtype.val hab)
  have ha : a ∈ center c.first := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    apply mul_right_cancel (b := (b : D))
    change ((k : D) * a) * b = ((a : D) * k) * b
    calc
      ((k : D) * a) * b = k * x := by rw [← hab']; group
      _ = x * k := mem_centralizer_iff.mp hx k k.property
      _ = ((a : D) * k) * b := by
        rw [← hab', mul_assoc, ← first_commutes_second c k b]
        group
  rw [first_center c, mem_bot] at ha
  rw [ha, Subgroup.coe_one, one_mul] at hab'
  exact hab' ▸ b.property

/-- Every nonabelian normal subgroup contains the actual first factor. -/
theorem first_le_of_normal_nonabelian (hS : Nat.card S = 8)
    (N : Subgroup D) [N.Normal] (hN : ⁅N,N⁆ ≠ ⊥) : c.first ≤ N := by
  let : IsSimpleGroup c.first := first_simple c
  let : c.first.Normal := first_normal c
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf c.first) inferInstance with h | h
  · have hi : Disjoint N c.first := by
      apply disjoint_def.mpr
      intro x hx hk
      have h1 : (⟨x,hk⟩ : c.first) = 1 := by
        apply mem_bot.mp
        rw [← h]
        exact hx
      exact congrArg Subtype.val h1
    have hc : N ≤ centralizer (c.first : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hi)
    have hn : N ≤ c.second := hc.trans (first_centralizer_le_second c hS)
    let : IsMulCommutative c.second := second_commutative c
    apply (hN _).elim
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hn hy⟩ : c.second) ⟨x,hn hx⟩)
  · intro x hx
    have hmem : (⟨x,hx⟩ : c.first) ∈ N.subgroupOf c.first := h ▸ mem_top _
    exact hmem

end LowRows.PrimeProduct
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection

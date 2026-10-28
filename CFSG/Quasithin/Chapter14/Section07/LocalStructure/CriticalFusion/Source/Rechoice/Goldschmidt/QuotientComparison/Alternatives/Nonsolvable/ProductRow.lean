module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Remaining
public import GorensteinWalter.PSL2PerfectOfCard


/-!
# Excluding the product row of F.6.18

The literal multiplication equivalence makes the PSL₂ factor normal in the
two-residual, hence subnormal in the ambient group. Its field congruence gives
order at least 660 and divisibility by four. The residual quotient is a
two-group, so the ambient Sylow order eight bounds its index by two. The outer
action on the cubic factor excludes index one.

The outer action on the PSL₂ factor then forces its ambient centralizer into
the residual, where its trivial center leaves only the cubic factor. The
simple-perfect subnormal dichotomy therefore excludes all three small models:
containment contradicts their order bound, and centralization makes them
abelian. The final application preserves the original subgroup through the
literal plus-to-bang quotient map.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18(3),
printed p.309, and the nonsolvable comparison in 14.7.70, printed p.1075.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource
namespace ProductRow
variable {D : Type*} [Group D] {S : Sylow 2 D} (r : FSource.ProductRow S)

private theorem field_card : Nat.card r.field.Carrier = r.field.prime := by
  rw [r.field.card, r.degree, pow_one]

private theorem field_lower : 11 ≤ Nat.card r.field.Carrier := by
  rw [field_card r]
  have := r.congruence
  omega

private theorem field_odd : Odd (Nat.card r.field.Carrier) := by
  rw [field_card r, Nat.odd_iff]
  have := r.congruence
  omega

private theorem first_card_lower : 660 ≤ Nat.card r.first := by
  rw [Nat.card_congr r.firstEquiv.toEquiv]
  exact pslTwo_order_ge_660 (field_odd r) (field_lower r)

private theorem first_simple : IsSimpleGroup r.first := by
  let : IsSimpleGroup PSL(2,r.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by have := field_lower r; omega)
  exact r.firstEquiv.isSimpleGroup

private theorem first_perfect : Group.IsPerfect r.first := by
  let : Group.IsPerfect PSL(2,r.field.Carrier) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by have := field_lower r; omega)
  exact Group.IsPerfect.ofSurjective (f := r.firstEquiv.symm.toMonoidHom) r.firstEquiv.symm.surjective

private theorem commute (a : r.first) (b : r.second) : (a : D) * b = b * a := by
  have h := congrArg (fun z : (r.first ⊔ r.second : Subgroup D) => (z : D))
    (r.product.map_mul ((1 : r.first), b) (a, (1 : r.second)))
  simpa only [Prod.mk_mul_mk, one_mul, mul_one, Subgroup.coe_mul, r.product_apply,
    Subgroup.coe_one] using h

private theorem second_centralizes : r.second ≤ centralizer (r.first : Set D) := by
  intro b hb
  exact mem_centralizer_iff.mpr (fun a ha => commute r ⟨a,ha⟩ ⟨b,hb⟩)

/-- The actual PSL₂ factor is subnormal through the literal two-residual. -/
theorem first_subnormal : r.first.IsSubnormal := by
  have hn : (r.first.subgroupOf (r.first ⊔ r.second)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le r.first.le_normalizer ((second_centralizes r).trans (Subgroup.centralizer_le_normalizer _)))
  have hr : (r.first ⊔ r.second).Normal := r.residual ▸ inferInstance
  exact .step _ _ le_sup_left hr.isSubnormal hn

private theorem decompose {x : D} (hx : x ∈ r.first ⊔ r.second) :
    ∃ a : r.first, ∃ b : r.second, x = a * b := by
  obtain ⟨⟨a,b⟩, h⟩ := r.product.surjective ⟨x,hx⟩
  exact ⟨a,b, (congrArg Subtype.val h).symm.trans (r.product_apply a b)⟩

private theorem conjugation_product (a x : r.first) (b : r.second) :
    ((a : D) * b) * x * ((a : D) * b)⁻¹ = (a : D) * x * (a : D)⁻¹ := by
  calc
    _ = (a : D) * ((b : D) * x * (b : D)⁻¹) * (a : D)⁻¹ := by group
    _ = _ := by rw [← commute r x b]; simp

private theorem second_commutative : IsMulCommutative r.second := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply r.secondEquiv.injective
  simp only [map_mul, mul_comm]

private theorem residual_centralizes_second : r.first ⊔ r.second ≤ centralizer (r.second : Set D) := by
  apply sup_le (le_centralizer_iff.mpr (second_centralizes r))
  exact le_centralizer_iff_isMulCommutative.mpr (second_commutative r)

private theorem element_not_mem : r.element ∉ r.first ⊔ r.second := by
  intro ht
  have htc := residual_centralizes_second r ht
  obtain ⟨α, hα, hout⟩ := r.secondOuter
  apply hout
  refine ⟨1, ?_⟩
  ext x
  simp only [map_one]
  rw [hα, ← mem_centralizer_iff.mp htc x x.property]
  simp

private theorem four_dvd_first : 4 ∣ Nat.card r.first := by
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (field_odd r)
  have hq := field_lower r
  have hm : Nat.card r.field.Carrier % 8 = 3 ∨ Nat.card r.field.Carrier % 8 = 5 := by
    rw [field_card r]
    have := r.congruence
    omega
  have hsq : (Nat.card r.field.Carrier ^ 2) % 8 = 1 := by
    rcases hm with hm | hm <;> norm_num [Nat.pow_mod, hm]
  have hsqpos : 1 ≤ Nat.card r.field.Carrier ^ 2 := by nlinarith
  have hd : 8 ∣ Nat.card r.field.Carrier * (Nat.card r.field.Carrier ^ 2 - 1) :=
    dvd_mul_of_dvd_right (by omega) _
  rw [← hc] at hd
  have : 4 ∣ Nat.card PSL(2,r.field.Carrier) :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp hd
  rwa [Nat.card_congr r.firstEquiv.toEquiv]

variable [Finite D]

include r in
/-- The residual has index two, using the cubic outer action to rule out index one. -/
theorem residual_index (hS : Nat.card S = 8) : (pResidual 2 D).index = 2 := by
  obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := D) 2).exists_card_eq
  have hi : (pResidual 2 D).index = 2 ^ n := by rwa [index_eq_card]
  have h4 : 4 ∣ Nat.card (pResidual 2 D) :=
    (four_dvd_first r).trans (card_dvd_of_le (r.residual ▸ le_sup_left))
  have hd : 2 ^ (2+n) ∣ Nat.card D := by
    rw [pow_add, ← (pResidual 2 D).card_mul_index, hi]
    exact Nat.mul_dvd_mul h4 dvd_rfl
  have hb := S.pow_dvd_card_of_pow_dvd_card hd
  rw [hS] at hb
  have hle : 2+n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.le_of_dvd (by decide : 0 < 8) hb)
  have hn0 : n ≠ 0 := by
    intro he
    have htop : pResidual 2 D = ⊤ := index_eq_one.mp (by simp [hi,he])
    exact element_not_mem r (by rw [← r.residual, htop]; trivial)
  have : n = 1 := by omega
  simp [hi,this]


private theorem centralizer_le_residual (hS : Nat.card S = 8) :
    centralizer (r.first : Set D) ≤ pResidual 2 D := by
  intro x hx
  by_contra hxR
  have htR : r.element ∉ pResidual 2 D := by rw [r.residual]; exact element_not_mem r
  have htx : r.element * x ∈ r.first ⊔ r.second := by
    rw [← r.residual, mul_mem_iff_of_index_two (residual_index r hS)]
    exact ⟨fun h => (htR h).elim, fun h => (hxR h).elim⟩
  obtain ⟨a,b,hab⟩ := decompose r htx
  obtain ⟨α,hα,hout⟩ := r.firstOuter
  apply hout
  refine ⟨a, ?_⟩
  ext k
  change (a : D) * k * (a : D)⁻¹ = (α k : D)
  rw [hα]
  calc
    _ = ((a : D) * b) * k * ((a : D) * b)⁻¹ := (conjugation_product r a k b).symm
    _ = (r.element * x) * k * (r.element * x)⁻¹ := by rw [hab]
    _ = r.element * (x * k * x⁻¹) * r.element⁻¹ := by group
    _ = _ := by rw [← mem_centralizer_iff.mp hx k k.property]; simp

omit [Finite D] in
private theorem first_center : center r.first = ⊥ := by
  let := first_simple r
  let := first_perfect r
  rcases (inferInstance : (center r.first).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative r.first (center_eq_top_iff.mp h)).elim

/-- The first outer action confines the PSL₂ centralizer to the cubic factor. -/
theorem centralizer_le_second (hS : Nat.card S = 8) :
    centralizer (r.first : Set D) ≤ r.second := by
  intro x hx
  obtain ⟨a,b,hab⟩ := decompose r (r.residual ▸ centralizer_le_residual r hS hx)
  have haC : (a : D) ∈ centralizer (r.first : Set D) := by
    have h := (centralizer (r.first : Set D)).mul_mem hx
      ((centralizer (r.first : Set D)).inv_mem (second_centralizes r b.property))
    simpa only [hab, mul_assoc, mul_inv_cancel, mul_one] using h
  have haZ : a ∈ center r.first := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.val_injective
    exact mem_centralizer_iff.mp haC k k.property
  have ha : a = 1 := by rwa [first_center r, mem_bot] at haZ
  rw [hab, ha, Subgroup.coe_one, one_mul]
  exact b.property

end ProductRow

/-- The actual small model has order at most 168. -/
private theorem SmallModel.card_le {H : Type*} [Group H] (hm : SmallModel H) : Nat.card H ≤ 168 := by
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- F.6.18(3) has no subnormal subgroup among the three retained small models. -/
theorem not_product_row {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (hS : Nat.card S = 8) (r : FSource.ProductRow S)
    (N : Subgroup D) (hN : N.IsSubnormal) (hm : SmallModel N) : False := by
  let := ProductRow.first_simple r
  let := ProductRow.first_perfect r
  rcases simple_subnormal_dichotomy r.first N (ProductRow.first_subnormal r) hN with hl | hc
  · have := (ProductRow.first_card_lower r).trans ((card_le_of_le hl).trans hm.card_le)
    omega
  · have hNC : N ≤ centralizer (r.first : Set D) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    have hNB : N ≤ r.second := hNC.trans (ProductRow.centralizer_le_second r hS)
    have hcomm : IsMulCommutative N := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      change (x : D) * (y : D) = (y : D) * (x : D)
      have h : ((⟨(x : D),hNB x.property⟩ : r.second) * ⟨(y : D),hNB y.property⟩) =
          (⟨(y : D),hNB y.property⟩ : r.second) * ⟨(x : D),hNB x.property⟩ := by
        apply r.secondEquiv.injective
        simp only [map_mul, mul_comm]
      exact congrArg (fun z : r.second => (z : D)) h
    exact hm.not_commutative hcomm

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (c : CriticalPath (L := L) F)

/-- The product row is excluded on the literal bang quotient of 14.7.70. -/
theorem not_bang_product_row (small : SmallSubnormal c)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) (hS : Nat.card S = 8)
    (r : FSource.ProductRow S) : False := by
  obtain ⟨N,_,_,hN,hm⟩ := retained_small_image c small
  exact not_product_row S hS r (N.map (plusToBang c)) hN hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

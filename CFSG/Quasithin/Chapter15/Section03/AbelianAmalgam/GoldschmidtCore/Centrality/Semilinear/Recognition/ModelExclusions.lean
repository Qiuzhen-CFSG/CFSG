module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.RankComparison
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.Mathieu.M12.Properties.ThreeRank
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Concrete rank and order exclusions for the F.6.18 rows

Cyclic Sylow three-subgroups pass to actual sections. This rules out a
noncyclic three-core, an extraspecial three-subgroup, alternating sections
of degree at least six, and M₁₂ sections. Each obstruction is a proved group
property, not a comparison of family labels. In particular the certified
Heisenberg subgroup of M₁₂ supplies an independent cubic plane.

The odd-field PSL₂ order formula excludes the prime parameters in rows (4)
and (5) from A₅ and the square-field component in row (8) from SL₃(2).
These are incompatibility tests for supplied group isomorphisms; no group
is recognized from its order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18,
pp.309–310, in the comparison used for 15.3.68, pp.1154–1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {D : Type u} [Group D] [Finite D]

/-- Every actual three-subgroup is cyclic under the ambient rank bound. -/
theorem three_subgroup_cyclic (hr : primeRank 3 D ≤ 1)
    (A : Subgroup D) (hA : IsPGroup 3 A) : IsCyclic A := by
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact isCyclic_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)

/-- This directly excludes the noncyclic-three-core row of F.6.18. -/
theorem threeCore_cyclic (hr : primeRank 3 D ≤ 1) : IsCyclic (pCore 3 D) :=
  three_subgroup_cyclic hr _ pCore_isPGroup

/-- An extraspecial three-subgroup cannot occur in an ambient three-rank-one group. -/
theorem no_extraspecial_three (hr : primeRank 3 D ≤ 1) (A : Subgroup D) :
    ¬ IsExtraspecial 3 A := by
  intro he
  let : IsExtraspecial 3 A := he
  let : IsCyclic A := three_subgroup_cyclic hr A (IsExtraspecial.isPGroup 3 A)
  let : Nontrivial (A ⧸ center A) := IsExtraspecial.quotient_nontrivial 3 A
  have hs : Subsingleton (A ⧸ center A) := by
    rw [Subgroup.center_eq_top]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (A ⧸ center A) hs

/-- The actual elementary nine in Aₙ excludes every alternating section
with n ≥ 6, including all the central-cover alternatives. -/
theorem no_alternating_section (hr : primeRank 3 D ≤ 1) (A : Subgroup D)
    {n : ℕ} (hn : 6 ≤ n) (q : A →* alternatingGroup (Fin n))
    (hq : Function.Surjective q) : False := by
  have hu := three_rank_section hr A q hq
  have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank hn
  omega

/-- The concrete Heisenberg Sylow subgroup excludes every actual M₁₂ section. -/
theorem no_mathieuTwelve_section (hr : primeRank 3 D ≤ 1) (A : Subgroup D)
    (q : A →* Sporadic.Mathieu.M12) (hq : Function.Surjective q) : False := by
  have hu := three_rank_section hr A q hq
  have hl := Sporadic.Mathieu.m12_three_rank_ge_two
  omega

/-- Two nontrivial cubic factors cannot embed together in a rank-one actor. -/
theorem no_cubic_product {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (hr : primeRank 3 D ≤ 1) (ha : 3 ∣ Nat.card A) (hb : 3 ∣ Nat.card B)
    (f : A × B →* D) (hf : Function.Injective f) : False := by
  have ha' : 1 ≤ primeRank 3 A := by
    have hn : primeRank 3 A ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h ha
    omega
  have hb' : 1 ≤ primeRank 3 B := by
    have hn : primeRank 3 B ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hb
    omega
  have hu := (primeRank_le_of_injective 3 f hf).trans hr
  rw [primeRank_prod_eq_add] at hu
  omega

/-- F.6.18(2)'s literal S₃ × S₃ model contains two independent cubics. -/
theorem no_symmetricThree_product (hr : primeRank 3 D ≤ 1)
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : False := by
  exact no_cubic_product hr
    (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
    (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
    e.symm.toMonoidHom e.symm.injective

variable {F : Type*} [Field F] [Finite F]

private theorem pslTwo_order_lower (hodd : Odd (Nat.card F)) {b : ℕ}
    (hb : b ≤ Nat.card F) : b * (b ^ 2 - 1) ≤ Nat.card PSL(2,F) * 2 := by
  rw [Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice hodd]
  exact Nat.mul_le_mul hb (Nat.sub_le_sub_right (Nat.pow_le_pow_left hb 2) 1)

/-- The actual odd-field rank-one component has order at least 660 when
its field has at least eleven elements. -/
theorem pslTwo_order_ge_660 (hodd : Odd (Nat.card F)) (hb : 11 ≤ Nat.card F) :
    660 ≤ Nat.card PSL(2,F) := by
  have h := pslTwo_order_lower hodd hb
  norm_num at h
  omega

/-- The square-field row has component order at least 360. -/
theorem pslTwo_order_ge_360 (hodd : Odd (Nat.card F)) (hb : 9 ≤ Nat.card F) :
    360 ≤ Nat.card PSL(2,F) := by
  have h := pslTwo_order_lower hodd hb
  norm_num at h
  omega

/-- The odd prime parameters ±11 modulo 24 cannot yield the A₅ component. -/
theorem primeRow_not_alternatingFive {p : ℕ} (_hp : Nat.Prime p)
    (hc : Nat.card F = p) (hm : p % 24 = 11 ∨ p % 24 = 13)
    (e : PSL(2,F) ≃* alternatingGroup (Fin 5)) : False := by
  have hodd : Odd (Nat.card F) := by rw [hc, Nat.odd_iff]; omega
  have hb : 11 ≤ Nat.card F := by rw [hc]; omega
  have hl := pslTwo_order_ge_660 hodd hb
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hl
  norm_num [Nat.factorial] at hl

/-- The field-extension component in row (8) is too large to be SL₃(2). -/
theorem squareFieldRow_not_binaryThree {p : ℕ} (_hp : Nat.Prime p)
    (hc : Nat.card F = p ^ 2) (hm : p % 8 = 3)
    (e : PSL(2,F) ≃* SL(3,ZMod 2)) : False := by
  have hodd : Odd (Nat.card F) := by
    rw [hc]
    exact (show Odd p from Nat.odd_iff.mpr (by omega)).pow
  have hb : 9 ≤ Nat.card F := by
    rw [hc]
    have h3 : 3 ≤ p := by omega
    nlinarith
  have hl := pslTwo_order_ge_360 hodd hb
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL] at hl
  omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

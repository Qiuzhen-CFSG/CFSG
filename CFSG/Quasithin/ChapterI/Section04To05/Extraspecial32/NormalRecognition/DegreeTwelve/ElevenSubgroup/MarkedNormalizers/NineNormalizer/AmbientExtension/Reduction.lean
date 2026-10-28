module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.Preparation
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Sylow placement and the centralizer alternative for the marked nine-group

The literal subgroup D = XX₁ extends to a Sylow three-subgroup of G of
order 27. Its index three in that subgroup makes it normal there, placing
the Sylow subgroup in N_G(D). The supplied semidihedral complement then
makes 432 divide the order of N_G(D).

Since z normalizes D and acts nontrivially on X₁, it lies outside C_G(D).
Adjoining z doubles the latter's order inside C_G(X), whose order is 18 or
54. Thus C_G(D) is D or a Sylow subgroup of order 27. In the second case
it is abelian, because its central subgroup D has cyclic quotient.

These are the initial reductions of Lemma 4.9, not the elimination of the
order-27 case or the construction of the marked GL₂(3) complement.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.9, p.41.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

private theorem sylow_three_card (s : SymmetricSixData h a) (B : Sylow 3 G) :
    Nat.card B = 27 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [B.card_eq_multiplicity, s.ambient_card]
  decide +kernel

/-- The Sylow extension is normal over D by its index three; no ambient normality of D is asserted. -/
public theorem exists_sylow_three_in_normalizer (s : SymmetricSixData h a) :
    ∃ B : Sylow 3 G, s.markedNine ≤ B ∧
      (B : Subgroup G) ≤ normalizer (s.markedNine : Set G) ∧ Nat.card B = 27 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 s.markedNine := IsPGroup.of_card
    (show Nat.card s.markedNine = 3 ^ 2 from s.card_markedNine)
  obtain ⟨B, hDB⟩ := hp.exists_le_sylow
  have hB := sylow_three_card s B
  have hD : Nat.card (s.markedNine.subgroupOf B) = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv, s.card_markedNine]
  have hi : (s.markedNine.subgroupOf B).index = 3 := by
    have hh := (s.markedNine.subgroupOf B).card_mul_index
    rw [hD, hB] at hh
    omega
  have hn : (s.markedNine.subgroupOf B).Normal :=
    normal_of_index_eq_minFac_card (by rw [hi, hB]; decide +kernel)
  exact ⟨B, hDB, (normal_subgroupOf_iff_le_normalizer hDB).mp hn, hB⟩

/-- The marked nine-group centralizes itself because it is elementary abelian. -/
public theorem markedNine_le_centralizer (s : SymmetricSixData h a) :
    s.markedNine ≤ centralizer (s.markedNine : Set G) := by
  let : IsElementaryAbelian 3 s.markedNine := s.elementary_markedNine
  exact s.markedNine.le_centralizer

private theorem z_not_mem_centralizer (s : SymmetricSixData h a) :
    z ∉ centralizer (s.markedNine : Set G) := by
  intro hz
  have hX : s.X1 = ⊥ := by
    apply bot_unique
    intro x hx
    have hxD : x ∈ s.markedNine := (show s.X1 ≤ s.markedNine from le_sup_right) hx
    have hc : x * z = z * x := hz x hxD
    have hi : x = x⁻¹ := by
      calc
        x = z * x * z⁻¹ := (mul_inv_eq_iff_eq_mul.mpr hc.symm).symm
        _ = x⁻¹ := s.z_inverts_X1 x hx
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      conv_lhs => lhs; rw [hi]
      exact inv_mul_cancel x
    have hx3 : orderOf x ∣ 3 := s.card_X1 ▸ s.X1.orderOf_dvd_natCard hx
    exact mem_bot.mpr (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
        (orderOf_dvd_of_pow_eq_one hx2) hx3))
  have hh := s.card_X1
  rw [hX, card_bot] at hh
  omega

/-- Doubling inside the actual centralizer of X leaves just the orders nine and 27. -/
public theorem centralizer_card_cases (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    Nat.card (centralizer (s.markedNine : Set G)) = 9 ∨
      Nat.card (centralizer (s.markedNine : Set G)) = 27 := by
  let C := centralizer (s.markedNine : Set G)
  have hzN : z ∈ normalizer (s.markedNine : Set G) := by
    have hP : m.P ≤ normalizer (s.markedNine : Set G) :=
      (show m.P ≤ s.markedNine ⊔ m.P from le_sup_right).trans
        (m.intersection ▸ inf_le_right)
    exact hP m.z_mem_P
  have hzC : z ∈ centralizer (cubicInG h : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((map_subtype_le _) hx)
  have hjoin : C ⊔ zpowers z ≤ centralizer (cubicInG h : Set G) :=
    sup_le (centralizer_le (show cubicInG h ≤ s.markedNine from le_sup_left))
      (zpowers_le.mpr hzC)
  have hcard : Nat.card (C ⊔ zpowers z : Subgroup G) = 2 * Nat.card C :=
    card_sup_zpowers_of_normalizing_involution C z
      (h.involution ▸ pow_orderOf_eq_one z) (z_not_mem_centralizer s)
      (normalizer_le_normalizer_centralizer s.markedNine hzN)
  have hd : Nat.card C ∣ 27 := by
    have hj := card_dvd_of_le hjoin
    rw [hcard] at hj
    rcases s.centralizer_X_card with he | he
    · rw [he] at hj
      exact dvd_trans ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hj) (by decide : 9 ∣ 27)
    · rw [he] at hj
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hj
  have hlo : 9 ≤ Nat.card C := s.card_markedNine ▸ card_le_of_le (markedNine_le_centralizer s)
  have hh : Nat.card C ∈ ({1, 3, 9, 27} : Finset ℕ) := by
    rw [← show (27 : ℕ).divisors = {1, 3, 9, 27} by decide +kernel]
    exact Nat.mem_divisors.mpr ⟨hd, by decide⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  change Nat.card C = 9 ∨ Nat.card C = 27
  rcases hh with hh | hh | hh | hh <;> omega

/-- The order-nine case is the literal D; the remaining centralizer is an ambient Sylow subgroup. -/
public theorem centralizer_eq_or_sylow (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    centralizer (s.markedNine : Set G) = s.markedNine ∨
      ∃ B : Sylow 3 G, (B : Subgroup G) = centralizer (s.markedNine : Set G) ∧
        Nat.card B = 27 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rcases centralizer_card_cases s m with hC | hC
  · exact Or.inl (eq_of_le_of_card_ge (markedNine_le_centralizer s)
      (by rw [hC, s.card_markedNine])).symm
  · let B : Sylow 3 G := Sylow.ofCard (centralizer (s.markedNine : Set G))
      (by rw [hC, s.ambient_card]; decide +kernel)
    exact Or.inr ⟨B, rfl, hC⟩

/-- The supplied complement normalizes the original embedded nine-group. -/
public theorem complement_le_normalizer (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    m.P ≤ normalizer (s.markedNine : Set G) :=
  (show m.P ≤ s.markedNine ⊔ m.P from le_sup_right).trans
    (m.intersection ▸ inf_le_right)

/-- The marked product DP gives the exact intersection order 144. -/
public theorem card_symmetric_normalizer_intersection
    (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    Nat.card ↥(normalizer (s.S : Set G) ⊓ normalizer (s.markedNine : Set G)) = 144 := by
  rw [m.intersection, card_sup_eq_mul_of_normalizes_of_disjoint
    s.markedNine m.P (complement_le_normalizer s m) m.disjoint,
    s.card_markedNine, m.card_P]

/-- Combining the product DP and the Sylow extension gives the source lower divisibility bound. -/
public theorem card_normalizer_divisible_by_432 (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    432 ∣ Nat.card (normalizer (s.markedNine : Set G)) := by
  have h144 : 144 ∣ Nat.card (normalizer (s.markedNine : Set G)) :=
    card_symmetric_normalizer_intersection s m ▸ card_dvd_of_le inf_le_right
  obtain ⟨B, -, hBN, hB⟩ := exists_sylow_three_in_normalizer s
  have h27 : 27 ∣ Nat.card (normalizer (s.markedNine : Set G)) := hB ▸ card_dvd_of_le hBN
  exact (show Nat.lcm 144 27 = 432 by decide) ▸ Nat.lcm_dvd h144 h27

/-- The order-four obstruction used after conjugating the fixed cubic subgroup to X. -/
public theorem centralizer_X_no_order_four (s : SymmetricSixData h a) (x : G)
    (hx : x ∈ centralizer (cubicInG h : Set G)) : orderOf x ≠ 4 := by
  intro ho
  have hd := (centralizer (cubicInG h : Set G)).orderOf_dvd_natCard hx
  rw [ho] at hd
  rcases s.centralizer_X_card with he | he <;> rw [he] at hd <;> norm_num at hd

/-- In the exceptional centralizer case, D is central of index three, forcing commutativity. -/
public theorem centralizer_abelian_of_card_twenty_seven (s : SymmetricSixData h a)
    (hC : Nat.card (centralizer (s.markedNine : Set G)) = 27) :
    IsMulCommutative (centralizer (s.markedNine : Set G)) := by
  let C := centralizer (s.markedNine : Set G)
  let D := s.markedNine.subgroupOf C
  have hDC := markedNine_le_centralizer s
  have hD : Nat.card D = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, s.card_markedNine]
  have hcenter : D ≤ center C := by
    intro x hx
    exact mem_center_iff.mpr (fun y => Subtype.ext ((y.property x hx).symm))
  have hn : D.Normal := by
    refine ⟨fun x hx y => ?_⟩
    have he : y * x * y⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hcenter hx) y)
    rw [he]
    exact hx
  let : D.Normal := hn
  have hi : D.index = 3 := by
    have hh := D.card_mul_index
    rw [hD, hC] at hh
    omega
  let : IsCyclic (C ⧸ D) := isCyclic_of_prime_card (show Nat.card (C ⧸ D) = 3 from hi)
  exact (QuotientGroup.mk' D).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa only [QuotientGroup.ker_mk'] using hcenter)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer

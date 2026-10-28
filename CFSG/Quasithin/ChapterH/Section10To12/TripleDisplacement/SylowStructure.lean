module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Mathieu.M22.Properties.Order
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The Sylow three-subgroups of genuine triple-M₂₂

The actual central quotient gives group order 1330560 and Sylow three order 27.
Central transfer puts the nontrivial cubic center of the perfect group into
its Sylow commutator subgroup. Hence the Sylow subgroup is nonabelian, and
its order identifies it as extraspecial with the same center as the ambient
cover. The cube homomorphism also supplies a noncentral order-three element.

This proves the group structure used in the second paragraph of the proof of
Aschbacher–Smith H.12.1, printed p.394 (combined 1 March 2004 manuscript).
Only the native M₂₂ order theorem is used; no split cover or multiplier label
stands in for the quasisimple central extension.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
/-- The order of the genuine central extension. -/
theorem triple_order (hL : IsTripleM22 L) : Nat.card L = 1330560 := by
  obtain ⟨e⟩ := hL.centralQuotient
  have hq : Nat.card (L ⧸ center L) = 443520 :=
    (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order
  rw [(center L).card_eq_card_quotient_mul_card_subgroup, hq, hL.center_card]

/-- Every Sylow three-subgroup has order 27. -/
theorem sylow_three_order (hL : IsTripleM22 L) (P : Sylow 3 L) :
    Nat.card (P : Subgroup L) = 27 := by
  rw [P.card_eq_multiplicity, triple_order hL]
  rw [show 1330560 = 3 ^ 3 * 49280 by norm_num,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  simp [Nat.Prime.factorization Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 49280)]

/-- Transfer rules out abelian Sylow three-subgroups. -/
theorem sylow_three_nonabelian (hL : IsTripleM22 L) (P : Sylow 3 L) :
    ¬ IsMulCommutative (P : Subgroup L) := by
  have hZP : center L ≤ (P : Subgroup L) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hL.center_card)).le_sylow_of_normal P
  have hd : _root_.commutator L = ⊤ := hL.quasisimple.toIsPerfect.commutator_eq_top
  have hzderived : center L ≤ ⁅(P : Subgroup L), (P : Subgroup L)⁆ := by
    intro z hz
    exact center_inf_commutator_inf_sylow_le_commutator P
      ⟨⟨hz, hd ▸ mem_top z⟩, hZP hz⟩
  intro hcomm
  let := hcomm
  have hbot : ⁅(P : Subgroup L), (P : Subgroup L)⁆ = ⊥ := by
    rw [← map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
  have hzbot : center L = ⊥ := le_bot_iff.mp (hbot ▸ hzderived)
  have hc := hL.center_card
  rw [hzbot, card_bot] at hc
  omega

/-- Extraspeciality and the equality of the centers, in the actual cover. -/
theorem sylow_three_structure (hL : IsTripleM22 L) (P : Sylow 3 L) :
    Nat.card (P : Subgroup L) = 27 ∧ IsExtraspecial 3 (P : Subgroup L) ∧
      (center (P : Subgroup L)).map (P : Subgroup L).subtype = center L := by
  have hp := sylow_three_order hL P
  have hn := sylow_three_nonabelian hL P
  have hz := OrderTwentySeven.center_card hp hn
  have hq : Nat.card ((P : Subgroup L) ⧸ center (P : Subgroup L)) = 3 ^ 2 :=
    OrderTwentySeven.quotient_center_card hp hn
  have hnc : ¬ IsCyclic ((P : Subgroup L) ⧸ center (P : Subgroup L)) := by
    intro h
    let := h
    exact hn (isMulCommutative_of_isCyclic_quotient_center_self (P : Subgroup L))
  have hex : IsExtraspecial 3 (P : Subgroup L) := {
    center_order_p := hz
    quotient_elementary_abelian := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
      exponent_dvd_p := by rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_three hq).mp hnc] }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hn (center_eq_top_iff.mp h)) }
  have hZP : center L ≤ (P : Subgroup L) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hL.center_card)).le_sylow_of_normal P
  have hle : center L ≤ (center (P : Subgroup L)).map (P : Subgroup L).subtype := by
    intro z hz
    refine ⟨⟨z, hZP hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (mem_center_iff.mp hz p)
  refine ⟨hp, hex, ?_⟩
  exact (eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (P : Subgroup L).subtype_injective, hz, hL.center_card])).symm
/-- Every Sylow three-subgroup contains a noncentral order-three actor. -/
theorem exists_noncentral_three_in_sylow (hL : IsTripleM22 L) (P : Sylow 3 L) :
    ∃ x : (P : Subgroup L), orderOf x = 3 ∧ x ∉ center (P : Subgroup L) := by
  have hp := sylow_three_order hL P
  have hn := sylow_three_nonabelian hL P
  have hz := OrderTwentySeven.center_card hp hn
  let f := OrderTwentySeven.cubeHom hp hn
  by_contra! h
  have hk : f.ker ≤ center (P : Subgroup L) := by
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have hx3 : x ^ 3 = 1 := by
        simpa only [f, OrderTwentySeven.cubeHom_apply] using MonoidHom.mem_ker.mp hx
      exact h x (orderOf_eq_prime hx3 hx1)
  have hr : f.range ≤ center (P : Subgroup L) := by
    rintro _ ⟨x, rfl⟩
    simpa only [f, OrderTwentySeven.cubeHom_apply] using
      OrderTwentySeven.cube_mem_center hp hn x
  have hkcard : Nat.card f.ker ≤ 3 := by simpa only [hz] using card_le_of_le hk
  have hrcard : Nat.card f.range ≤ 3 := by simpa only [hz] using card_le_of_le hr
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, hp] at hc
  nlinarith

/-- An actual noncentral cubic actor in the cover. -/
theorem exists_noncentral_three (hL : IsTripleM22 L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ center L := by
  let P : Sylow 3 L := Classical.choice inferInstance
  obtain ⟨x, hx, hnx⟩ := exists_noncentral_three_in_sylow hL P
  refine ⟨x, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hx
  · intro h
    apply hnx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp h (y : L))

omit [Finite L] in
/-- The odd-prime cases include seven, as well as three, five and eleven. -/
theorem odd_prime_order_cases (hL : IsTripleM22 L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (x : L) (hx : orderOf x = p) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hL.centralQuotient
  have hd : p ∣ Nat.card L := hx ▸ orderOf_dvd_natCard x
  rw [(center L).card_eq_card_quotient_mul_card_subgroup, hL.center_card,
    Nat.card_congr e.toEquiv] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · have hs := (Sporadic.Mathieu.m22_prime_dvd_order_iff p).mp h
    exact hs.resolve_left hp2
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement

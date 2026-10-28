module

public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution

/-!
# Extraspecial central products and noncyclic factors of order eight

Two commuting extraspecial two-groups with intersection of order two generate
an extraspecial group. The shared subgroup is the image of each factor center.
Writing a central element as a product of factor elements identifies the whole
center with this intersection. Squares are central, so the central quotient
is elementary abelian.

If the ambient two-group has cyclic center, a noncyclic commuting factor is
nonabelian. At order eight it is therefore extraspecial, and the central-product
order formula makes the product of two such factors extraspecial of order 32.
This permits absorbing a small Hall tail into the extraspecial factor.

Source: the central-product calculations in Janko–Thompson, Math. Z. 113
(1970), §4, pp.392–393; the extraspecial definition and the prime-cube center
calculation suffice for this intrinsic step.
-/

open Subgroup
open scoped IsMulCommutative

/-- A nonabelian group of order eight is extraspecial. -/
public theorem IsExtraspecial.of_noncommutative_card_eight
    {P : Type*} [Group P] [Finite P]
    (hc : Nat.card P = 8) (hn : ¬ IsMulCommutative P) : IsExtraspecial 2 P := by
  have hz : Nat.card (center P) = 2 :=
    card_center_eq_prime_of_card_eq_prime_cube (p := 2) hc hn
  have hq : Nat.card (P ⧸ center P) = 2 ^ 2 := by
    have h := (center P).card_mul_index
    rw [hz, hc, index_eq_card] at h
    omega
  have hnc : ¬ IsCyclic (P ⧸ center P) := by
    intro h
    let := h
    exact hn (isMulCommutative_of_isCyclic_quotient_center_self P)
  exact {
    center_order_p := hz
    quotient_elementary_abelian := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
      exponent_dvd_p := by rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_two hq).mp hnc] }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hn (center_eq_top_iff.mp h)) }

namespace Subgroup

/-- Commuting extraspecial two-subgroups with common center of order two
generate an extraspecial group. -/
public theorem isExtraspecial_of_central_product
    {P : Type*} [Group P] [Finite P]
    (A D : Subgroup P) [A.Normal] [IsExtraspecial 2 A] [IsExtraspecial 2 D]
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (hi : Nat.card (A ⊓ D : Subgroup P) = 2) : IsExtraspecial 2 P := by
  have hIA : A ⊓ D = (center A).map A.subtype := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨ha, hd⟩
      exact ⟨⟨x, ha⟩, mem_center_iff.mpr (fun a => Subtype.ext (hc hd a a.property)), rfl⟩
    · rw [card_map_of_injective A.subtype_injective, IsExtraspecial.center_order_p 2 _, hi]
  have hID : A ⊓ D = (center D).map D.subtype := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨ha, hd⟩
      exact ⟨⟨x, hd⟩, mem_center_iff.mpr
        (fun d => Subtype.ext ((hc d.property x ha).symm)), rfl⟩
    · rw [card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 2 _, hi]
  have hdecomp (x : P) : ∃ a ∈ A, ∃ d ∈ D, a * d = x :=
    mem_sup_of_normal_left.mp (hg ▸ mem_top x)
  have hIZ : A ⊓ D ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, ha, d, hd, rfl⟩ := hdecomp y
    calc
      a * d * x = a * (d * x) := mul_assoc _ _ _
      _ = a * (x * d) := by rw [(hc hd x hx.1).symm]
      _ = x * (a * d) := by rw [← mul_assoc, hc hx.2 a ha, mul_assoc]
  have hZA : (center A).map A.subtype ≤ center P := hIA ▸ hIZ
  have hZD : (center D).map D.subtype ≤ center P := hID ▸ hIZ
  have hcenter : center P = A ⊓ D := by
    apply le_antisymm ?_ hIZ
    intro x hx
    obtain ⟨a, ha, d, hd, rfl⟩ := hdecomp x
    have haZ : (⟨a, ha⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro b
      apply Subtype.ext
      apply mul_right_cancel (b := d)
      calc
        (b : P) * a * d = (b : P) * (a * d) := mul_assoc _ _ _
        _ = (a * d) * b := mem_center_iff.mp hx b
        _ = a * b * d := by rw [mul_assoc, ← hc hd b b.property, ← mul_assoc]
    have hdZ : (⟨d, hd⟩ : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro b
      apply Subtype.ext
      apply mul_left_cancel (a := a)
      calc
        a * ((b : P) * d) = (b : P) * (a * d) := by
          rw [← mul_assoc, hc b.property a ha, mul_assoc]
        _ = (a * d) * b := mem_center_iff.mp hx b
        _ = a * (d * b) := mul_assoc _ _ _
    exact (A ⊓ D).mul_mem (hIA ▸ mem_map_of_mem A.subtype haZ)
      (hID ▸ mem_map_of_mem D.subtype hdZ)
  have hsquare (x : P) : x ^ 2 ∈ center P := by
    obtain ⟨a, ha, d, hd, rfl⟩ := hdecomp x
    rw [(show Commute a d from hc hd a ha).mul_pow]
    exact (center P).mul_mem
      (hZA (mem_map_of_mem A.subtype (IsExtraspecial.square_mem_center (⟨a, ha⟩ : A))))
      (hZD (mem_map_of_mem D.subtype (IsExtraspecial.square_mem_center (⟨d, hd⟩ : D))))
  have hqpow (x : P ⧸ center P) : x ^ 2 = 1 := by
    induction x using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff _).mpr (hsquare x)
  have hinv (x : P ⧸ center P) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hqpow x)
  refine {
    center_order_p := hcenter ▸ hi
    quotient_elementary_abelian := {
      toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hqpow }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }
  · calc
      x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y * x := by rw [mul_inv_rev, hinv, hinv]
  · intro htop
    have hAtop : center A = ⊤ := by
      apply top_unique
      intro a _
      have haP : (a : P) ∈ center P := htop ▸ mem_top (a : P)
      exact mem_center_iff.mpr (fun b => Subtype.ext (mem_center_iff.mp haP (b : P)))
    let : Nontrivial (A ⧸ center A) := IsExtraspecial.quotient_nontrivial 2 A
    exact QuotientGroup.nontrivial_iff.mp inferInstance hAtop

/-- A noncyclic factor in a commuting product with cyclic center is nonabelian. -/
public theorem noncommutative_factor_of_noncyclic_of_cyclic_center
    {P : Type*} [Group P] [IsCyclic (center P)]
    (A D : Subgroup P) (hc : D ≤ centralizer (A : Set P))
    (hg : A ⊔ D = ⊤) (hn : ¬ IsCyclic D) : ¬ IsMulCommutative D := by
  intro hcomm
  let : IsMulCommutative D := hcomm
  have hDZ : D ≤ center P := by
    have htop : (⊤ : Subgroup P) ≤ centralizer (D : Set P) := by
      rw [← hg]
      exact sup_le (le_centralizer_iff.mp hc) (le_centralizer D)
    simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp htop
  exact hn (isCyclic_of_injective (inclusion hDZ) (inclusion_injective hDZ))

/-- Two commuting factors of order eight, one extraspecial and the other
noncyclic, make an extraspecial group of order thirty-two when the center is cyclic. -/
public theorem extraspecial_card_thirty_two_of_noncyclic_eight_factors
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8) (hD : Nat.card D = 8)
    (hn : ¬ IsCyclic D) (hc : D ≤ centralizer (A : Set P))
    (hg : A ⊔ D = ⊤) : IsExtraspecial 2 P ∧ Nat.card P = 32 := by
  let : IsExtraspecial 2 D := IsExtraspecial.of_noncommutative_card_eight hD
    (noncommutative_factor_of_noncyclic_of_cyclic_center A D hc hg hn)
  have hDne : D ≠ ⊥ := by intro h; simp [h] at hD
  have hi := card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hDne hc
  have hord := card_mul_two_eq_of_extraspecial_of_cyclic_center hP A D hDne hc hg
  exact ⟨isExtraspecial_of_central_product A D hc hg hi, by rw [hA, hD] at hord; omega⟩

end Subgroup

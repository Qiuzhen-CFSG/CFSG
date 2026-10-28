module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import Theory.Representation.BinaryNaturalDual

/-!
# The involution coset in the actual vector quotient

An involution swapping complementary binary summands has every fixed vector
in its displacement image. Applied to the literal conjugation action on
`U/Z`, this conjugates all involutions in the outside coset modulo `Z`.
The hypotheses describe the swapped summands and an intertwining coordinate
isomorphism, not the desired conjugacy conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58(3) and the proof of 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
open scoped CharTwo
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G : Type*} [Group G]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem binary_neg (w : W) : -w = w := by
  simpa only [CharTwo.neg_eq, one_smul] using (neg_smul (1 : ZMod 2) w).symm

/-- The cocycle of an involution swapping complementary binary summands is principal. -/
theorem swapped_norm_one_is_displacement {Q : Type*} [Group Q]
    (e : Q ≃* Multiplicative W) (σ : MulAut Q) (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (σ q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hs : Function.Involutive s)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A)
    (x : Q) (hx : σ x * x = 1) :
    ∃ u : Q, u⁻¹ * σ u = x := by
  have hnorm : s (e x).toAdd + (e x).toAdd = 0 := by
    have h := congrArg (fun q => (e q).toAdd) hx
    simpa only [map_mul, he, map_one, toAdd_mul,
      toAdd_ofAdd, toAdd_one] using h
  have hfix : s (e x).toAdd = (e x).toAdd := by
    exact (eq_neg_of_add_eq_zero_left hnorm).trans (binary_neg _)
  obtain ⟨w, hw⟩ := (BinaryNaturalDual.fixed_iff_displacement hAB s hs hA hB _).mp hfix
  refine ⟨e.symm (Multiplicative.ofAdd w), ?_⟩
  apply e.injective
  apply Multiplicative.toAdd.injective
  simpa only [map_mul, map_inv, he, e.apply_symm_apply, toAdd_mul,
    toAdd_inv, toAdd_ofAdd, sub_eq_add_neg, add_comm] using hw

/-- The actual `U/Z` calculation conjugates an involution coset modulo `Z`.
The coordinate equivalence is required to intertwine `quotientAction`. -/
theorem swapped_quotient_coset_transitive
    (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1)
    (e : VectorQuotient Z ZS ≃* Multiplicative W)
    (s : W ≃ₗ[ZMod 2] W)
    (he : ∀ q, e (quotientAction Z ZS t q) = Multiplicative.ofAdd (s (e q).toAdd))
    (A B : Submodule (ZMod 2) W) (hAB : IsCompl A B)
    (hA : ∀ w ∈ A, s w ∈ B) (hB : ∀ w ∈ B, s w ∈ A)
    (x : closureU Z ZS) (hx : ((x : G) * (t : G)) ^ 2 ∈ Z) :
    ∃ u : closureU Z ZS,
      (u : G)⁻¹ * (t : G) * (u : G) * ((x : G) * (t : G))⁻¹ ∈ Z := by
  let q := QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))
  let σ := quotientAction Z ZS t
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
  have htH : t ^ 2 = 1 := Subtype.ext ht
  have hs : Function.Involutive s := by
    intro w
    obtain ⟨a, ha⟩ := e.surjective (Multiplicative.ofAdd w)
    have hsigma : σ (σ a) = a := by
      have h := congrArg (fun b : centralizerH Z => quotientAction Z ZS b a) htH
      simpa only [pow_two, map_mul, MulAut.mul_apply, map_one, MulAut.one_apply] using h
    have h := congrArg (fun b => (e b).toAdd) hsigma
    simpa only [σ, he, ha, toAdd_ofAdd] using h
  let y : closureU Z ZS := ⟨(t : G) * (x : G) * (t : G)⁻¹,
    (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS t.property) x).mp x.property⟩
  have hy : σ (q x) = q y := quotientAction_mk Z ZS t x
  have hnorm : σ (q x) * q x = 1 := by
    rw [hy, ← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (t : G) * (x : G) * (t : G)⁻¹ * (x : G) ∈ Z
    have hn := (Subgroup.centralizer_le_normalizer (Z : Set G)) t.property
    have hh := (mem_normalizer_iff.mp hn (((x : G) * (t : G)) ^ 2)).mp hx
    have heq : (t : G) * (((x : G) * (t : G)) ^ 2) * (t : G)⁻¹ =
        (t : G) * (x : G) * (t : G) * (x : G) := by simp [pow_two, mul_assoc]
    rw [heq] at hh
    simpa only [htinv] using hh
  obtain ⟨a, ha⟩ := swapped_norm_one_is_displacement e σ s he A B hAB hs hA hB (q x) hnorm
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) a
  let u' : closureU Z ZS := ⟨(t : G) * (u : G) * (t : G)⁻¹,
    (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS t.property) u).mp u.property⟩
  have hqu : σ (q u) = q u' := quotientAction_mk Z ZS t u
  have hzero : q (u⁻¹ * u' * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hqu, ha, mul_inv_cancel]
  have hz := (QuotientGroup.eq_one_iff _).mp hzero
  refine ⟨u, ?_⟩
  change (u : G)⁻¹ * ((t : G) * (u : G) * (t : G)⁻¹) * (x : G)⁻¹ ∈ Z at hz
  convert hz using 1; group

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic

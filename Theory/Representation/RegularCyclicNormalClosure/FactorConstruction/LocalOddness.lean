module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.QuotientGeometry

/-!
# Direct oddness of the local fixer in the transitive branch

Every involution in the pointwise fixer preserves the original fixed space
and hence both summands. It fixes F, so its rank on U is at most dim(U/F).
Its square-zero displacement on S has rank at most half dim S. The actual
transitive geometry inequality gives twice dim(U/F) at most dim S, forcing
ambient rank at most dim S and contradicting the original input.

This is a specialized local argument for Aschbacher–Smith E.6.24, printed
p.255. It avoids GLS C.14.2 Step 3's general Singer-normalizer and induction
arguments. It does not prove the transitive-geometry premise or promote any
odd-order theorem into Theory.
-/

public section

open Module Subgroup Representation.BinaryOffender
open Representation.GoldschmidtONan (orbit_map_one)
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- In the transitive dimension range, involutions in the pointwise fixer
would have ambient rank at most the original moved dimension. -/
theorem Input.odd_pointwiseFixer_of_dimension (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤
        finrank (ZMod 2) F)
    (hsmall : 2 * (finrank (ZMod 2) (fixedSpace ρ C) - finrank (ZMod 2) F) ≤
      finrank (ZMod 2) (displacementSpan ρ C ⊤)) :
    Odd (Nat.card (pointwiseFixer ρ F)) := by
  by_contra hodd
  have hdiv : 2 ∣ Nat.card (pointwiseFixer ρ F) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := pointwiseFixer ρ F) 2 hdiv
  have htA : orderOf (t : A) = 2 := (orderOf_injective
    (pointwiseFixer ρ F).subtype Subtype.val_injective t).trans ht
  have hU := h.involution_preserves_local_orbit F hFU hmax t 1 htA
  simp only [Subgroup.coe_one, orbit_map_one] at hU
  have hS := displacementSpan_map_of_normalized ρ C t (h.normal_in_stabilizer t hU)
  have hb := fixedCodim_le_of_split ρ (t : A)
    (by simpa only [← htA] using pow_orderOf_eq_one (t : A))
    (fixedSpace ρ C) (displacementSpan ρ C ⊤) F h.split hFU
    ((mem_pointwiseFixer ρ F t).mp t.property) hS.le hsmall
  exact (Nat.not_lt_of_ge hb) (h.no_small_involutions (t : A) htA)

/-- The numerical clause of the actual quotient transitive geometry
suffices for oddness of the pointwise fixer, without GLS Step 3 or induction. -/
theorem Input.odd_pointwiseFixer_of_transitiveGeometry (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤
        finrank (ZMod 2) F)
    (hgeom : GoldschmidtONan.TransitiveGeometry (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) : Odd (Nat.card (pointwiseFixer ρ F)) := by
  apply h.odd_pointwiseFixer_of_dimension F hFU hmax
  have hh := hgeom.2.2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))),
    Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := displacementSpan (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ⊤),
    Nat.card_zmod] at hh
  rw [← pow_mul,
    Nat.pow_le_pow_iff_right (by decide : 1 < 2), h.moved_finrank_quotientOnFixer F hFU] at hh
  have hf := h.fixed_finrank_quotientOnFixer F hFU
  omega

end Representation.RegularCyclicNormalClosure

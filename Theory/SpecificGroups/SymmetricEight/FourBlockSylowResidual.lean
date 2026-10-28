module
public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Sylow supplements in the four-block local group

The literal stabilizer of two four-point blocks has order 2⁷ · 3², by its
structural wreath-product coordinates. Its prime-to-three residual quotient
is consequently a two-group, and every Sylow two-subgroup supplements that
residual. Intersecting the stabilizer with A₈ leaves the embedded O^{3′}
unchanged because the alternating subgroup has prime-to-three index.

This is the exact local generation used after Aschbacher–Smith 13.6.23,
printed p.933 (combined manuscript, 1 March 2004). No chosen Sylow marking,
residual classification, or enumeration of S₈ is required.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual
open A6ShadowTwoLocals

/-- The order follows from the literal S₄ wreath C₂ coordinates. -/
theorem fourStabilizer_card : Nat.card fourStabilizer = 1152 := by
  rw [Nat.card_congr FourBlockQuotient.fourStabilizerWreathEquiv.toEquiv,
    RegularWreathProduct.card, Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card]

/-- Killing O^{3′} leaves only the two-part of the block stabilizer. -/
theorem residual_quotient_two : IsPGroup 2 (fourStabilizer ⧸ primeToResidual 3 fourStabilizer) := by
  apply (isPGroup_iff_card_dvd_pow).mpr
  refine ⟨7, ?_⟩
  rw [← index_eq_card]
  have hd := (primeToResidual 3 fourStabilizer).index_dvd_card
  rw [fourStabilizer_card, show 1152 = 2 ^ 7 * 3 ^ 2 by decide] at hd
  have hc : Nat.Coprime (primeToResidual 3 fourStabilizer).index (3 ^ 2) :=
    (primeToResidual_index_coprime (G := fourStabilizer) 3).symm.pow_right 2
  exact hc.dvd_of_dvd_mul_right hd

/-- The even block stabilizer has the same embedded prime-to-three residual. -/
theorem residual_even_eq :
    (primeToResidual 3 (alternatingGroup (Fin 8) ⊓ fourStabilizer : Subgroup S8)).map
      (alternatingGroup (Fin 8) ⊓ fourStabilizer).subtype =
        (primeToResidual 3 fourStabilizer).map fourStabilizer.subtype := by
  apply embedded_primeToResidual_inf_eq_of_normal
  apply primeToResidual_le
  rw [alternatingGroup.index_eq_two]
  decide

/-- Any actual Sylow two-subgroup supplements the even block residual. -/
theorem residual_sup_sylow (S : Sylow 2 fourStabilizer) :
    (primeToResidual 3 (alternatingGroup (Fin 8) ⊓ fourStabilizer : Subgroup S8)).map
      (alternatingGroup (Fin 8) ⊓ fourStabilizer).subtype ⊔
      (S : Subgroup fourStabilizer).map fourStabilizer.subtype = fourStabilizer := by
  have hp : pResidual 2 fourStabilizer ≤ primeToResidual 3 fourStabilizer :=
    sInf_le ⟨inferInstance, residual_quotient_two⟩
  have he : primeToResidual 3 fourStabilizer ⊔ (S : Subgroup fourStabilizer) = ⊤ :=
    top_unique ((pResidual_sup_sylow_eq_top S).ge.trans (sup_le_sup_right hp _))
  rw [residual_even_eq, ← Subgroup.map_sup, he, ← MonoidHom.range_eq_map, range_subtype]

end Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual

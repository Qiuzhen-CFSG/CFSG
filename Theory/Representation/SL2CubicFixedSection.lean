module

public import Theory.Representation.BinaryOffender.Defs
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Cubic fixed spaces on a natural SL₂-section

In characteristic two, an upper triangular determinant-one matrix of order
three has neither diagonal entry equal to one. Its natural fixed space is
therefore zero. If the section `D/C_D(L)` is equivariantly identified with
the natural plane, a subgroup containing such a cubic element has no extra
fixed vectors in `D`. The identification includes an actual multiplicative
equivalence of actors and binary linear coordinates on the quotient.

Source: the natural-module calculation in Aschbacher–Smith, combined
manuscript (1 March 2004), proof of 15.3.49, printed p.1144. The calculation
holds over every field of characteristic two; it uses no model recognition.
-/

@[expose] public section

open Subgroup Matrix Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative

namespace Representation.SL2CubicFixedSection

variable {F : Type*} [Field F] [CharP F 2]

/-- A cubic element of the rank-one Borel fixes no nonzero natural vector. -/
lemma cubic_borel_fixed_eq_zero (g : SL(2, F)) (hg : orderOf g = 3)
    (hB : g ∈ SpecialLinearGroup.rankOneBorel F)
    (v : Fin 2 → F) (hv : g.val *ᵥ v = v) : v = 0 := by
  have h10 := (SpecialLinearGroup.mem_rankOneBorel_iff g).mp hB
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two, h10, mul_zero, sub_zero] using g.property
  have h00 : g.val 0 0 ≠ 1 := by
    intro h
    have h11 : g.val 1 1 = 1 := by simpa only [h, one_mul] using hd
    have hs : g ^ 2 = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_two, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one,
          Matrix.mul_apply, Fin.sum_univ_two, h, h10, h11, CharTwo.add_self_eq_zero]
    have hn : 3 ∣ 2 := hg ▸ orderOf_dvd_of_pow_eq_one hs
    norm_num at hn
  have h11 : g.val 1 1 ≠ 1 := by
    intro h
    exact h00 (by simpa only [h, mul_one] using hd)
  have h1 : g.val 1 1 * v 1 = v 1 := by
    simpa only [mulVec, dotProduct, Fin.sum_univ_two, h10, zero_mul, zero_add] using congrFun hv 1
  have hv1 : v 1 = 0 := by
    have he : (g.val 1 1 - 1) * v 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h11)
  have h0 : g.val 0 0 * v 0 = v 0 := by
    simpa only [mulVec, dotProduct, Fin.sum_univ_two, hv1, mul_zero, add_zero] using congrFun hv 0
  have hv0 : v 0 = 0 := by
    have he : (g.val 0 0 - 1) * v 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h00)
  ext i
  fin_cases i <;> assumption

variable [Algebra (ZMod 2) F]
variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- Coordinates on the literal component section, with the quotient by its fixed space explicit. -/
structure NaturalComponentSection (ρ : Representation (ZMod 2) K W)
    (L : Subgroup K) (D : Submodule (ZMod 2) W) where
  model : L ≃* SL(2, F)
  invariant : ∀ (l : L) (d : D), ρ l d ∈ D
  coordinates : (D ⧸ (fixedSpace ρ L).comap D.subtype) ≃ₗ[ZMod 2] (Fin 2 → F)
  equivariant : ∀ (l : L) (d : D),
    coordinates ((Submodule.Quotient.mk ⟨ρ l d, invariant l d⟩)) =
      (model l).val *ᵥ coordinates (Submodule.Quotient.mk d)

/-- A cubic Borel element kills the fixed space on the natural section. -/
lemma fixedSpace_le_of_natural_section
    (ρ : Representation (ZMod 2) K W) (L Y : Subgroup K)
    (D : Submodule (ZMod 2) W) (sectionModel : NaturalComponentSection (F := F) ρ L D)
    (hYL : Y ≤ L) (hcubic : ∃ y : Y, orderOf y = 3)
    (hB : ∀ y : Y, sectionModel.model ⟨y, hYL y.property⟩ ∈ SpecialLinearGroup.rankOneBorel F) :
    D ⊓ fixedSpace ρ Y ≤ fixedSpace ρ L := by
  obtain ⟨y, hy⟩ := hcubic
  let l : L := ⟨y, hYL y.property⟩
  have horder : orderOf (sectionModel.model l) = 3 := by
    rw [sectionModel.model.orderOf_eq]
    exact (Subgroup.orderOf_coe l).symm.trans ((Subgroup.orderOf_coe y).trans hy)
  intro d hd
  let dD : D := ⟨d, hd.1⟩
  have he := sectionModel.equivariant l dD
  have hdY : ρ l d = d := hd.2 y
  have hdD : (⟨ρ l dD, sectionModel.invariant l dD⟩ : D) = dD := Subtype.ext hdY
  rw [hdD] at he
  have hz := cubic_borel_fixed_eq_zero (sectionModel.model l) horder (hB y)
    (sectionModel.coordinates (Submodule.Quotient.mk dD)) he.symm
  have hq : (Submodule.Quotient.mk dD : D ⧸ (fixedSpace ρ L).comap D.subtype) = 0 :=
    sectionModel.coordinates.injective (hz.trans sectionModel.coordinates.map_zero.symm)
  change dD ∈ (fixedSpace ρ L).comap D.subtype
  exact (Submodule.Quotient.mk_eq_zero _).mp hq


end Representation.SL2CubicFixedSection

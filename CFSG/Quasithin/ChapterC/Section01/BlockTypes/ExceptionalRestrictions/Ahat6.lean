module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6Cubic
public import Theory.Representation.CentralCubicRestriction
public import Mathlib.GroupTheory.Sylow

/-!
# The exceptional triple cover inside SL₃(F₄)

Choose a generator of the actual order-three center of L/O₂(L). The block
interval and commutator generation prove its quadratic scalar relation.
The recovered F₄ structure has dimension three and the perfect quotient
acts with determinant one. Thus the constructed injective homomorphism and
coordinates identify the original U with the restricted natural module.

Source: Aschbacher--Smith C.1.22, printed p.129, with the triple-cover
convention of A.3.5, printed p.43. No universal sixfold cover is substituted.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L]

/-- The recovered scalar field really has four elements. -/
theorem exceptionalScalarField_card : Nat.card CentralCubicRestriction.F = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact SL2FourNatural.card_field

/-- The original U has binary dimension six. -/
theorem IsExceptionalAhat6Block.u_finrank (h : IsExceptionalAhat6Block L) :
    letI := h.1.elementary
    Module.finrank (ZMod 2) (Additive (blockU L)) = 6 := by
  let := h.1.finite
  let := h.1.elementary
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) (Additive (blockU L)) = Nat.card (Additive (blockU L)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = Nat.card (blockU L) := Nat.card_congr Additive.toMul
    _ = 2 ^ 6 := h.2.2.2.2.1

/-- The faithful natural restriction of the source's actual triple cover.
The field, field-module structure, group embedding, and intertwining coordinates
are all conclusions of the original exceptional-block predicate. -/
theorem IsExceptionalAhat6Block.natural_restriction (h : IsExceptionalAhat6Block L) :
    letI := h.1.elementary
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      ∃ (_ : Algebra (ZMod 2) F) (m : Module F (Additive (blockU L))), letI := m
        IsScalarTower (ZMod 2) F (Additive (blockU L)) ∧
        ∃ (f : (L ⧸ pCore 2 L) →* Matrix.SpecialLinearGroup (Fin 3) F)
          (e : Additive (blockU L) ≃ₗ[F] (Fin 3 → F)),
          Function.Injective f ∧ ∀ (l : L) (u : blockU L),
            e (Additive.ofMul (blockConjugate L l u)) =
              specialLinearNatural 3 (f (QuotientGroup.mk' (pCore 2 L) l)) (e (Additive.ofMul u)) := by
  let := h.1.finite
  let := h.1.elementary
  let := h.2.1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center (L ⧸ pCore 2 L)) 3
    (by rw [h.2.2.1])
  have hne : (z : L ⧸ pCore 2 L) ≠ 1 := by
    intro he
    have he' : z = 1 := Subtype.ext he
    rw [he', orderOf_one] at hz
    contradiction
  have hz3 : (z : L ⧸ pCore 2 L) ^ 3 = 1 := by
    have hh : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
    exact congrArg Subtype.val hh
  have hq := central_cubic_quadratic h z z.property hne hz3
  obtain ⟨m, ht, f, e, hf, he⟩ := CentralCubicRestriction.exists_natural_restriction
    (uRepresentation h.1) z z.property hq (uRepresentation_faithful h) h.u_finrank
  refine ⟨CentralCubicRestriction.F, inferInstance, inferInstance, exceptionalScalarField_card,
    inferInstance, m, ht, f, e, hf, ?_⟩
  intro l u
  exact he (QuotientGroup.mk' (pCore 2 L) l) (Additive.ofMul u)
end CFSG.Quasithin.ChapterC

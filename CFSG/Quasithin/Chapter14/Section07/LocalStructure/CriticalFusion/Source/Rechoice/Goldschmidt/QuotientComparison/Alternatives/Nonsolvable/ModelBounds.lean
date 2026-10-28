module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.Component
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds

/-!
# Classical component exclusions for the small-subnormal comparison

The actual component has order 168 or 60. Existing PSL₂ order bounds
exclude the prime and square-field components. Defining-prime cubes
exclude all four special/projective linear/unitary degree-three models.
The actual M₁₂ component is likewise too large. These arguments use the
quasisimplicity supplied by F.6, without a bound on ambient three-rank.

Source: Aschbacher–Smith, Lemma 14.7.70, printed p.1075, using
F.6.18(4),(5),(8),(11),(13), printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource
variable {D : Type*} [Group D] [Finite D]

/-- Only the order bound is used in excluding the larger F.6 components. -/
theorem fitting_card_le (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D)) : Nat.card (generalizedFitting D) ≤ 168 := by
  rcases fitting_small_models K hK hm hq with he | he <;> obtain ⟨e⟩ := he
  · rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- The prime PSL₂ component in rows (4) and (5) is too large. -/
theorem not_prime_linear_component (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D))
    (f : FieldParameter) (hd : f.degree = 1)
    (hc : f.prime % 24 = 11 ∨ f.prime % 24 = 13)
    (e : generalizedFitting D ≃* PSL(2,f.Carrier)) : False := by
  have hf : Nat.card f.Carrier = f.prime := by rw [f.card, hd, pow_one]
  have ho : Odd (Nat.card f.Carrier) := by rw [hf, Nat.odd_iff]; omega
  have hb : 11 ≤ Nat.card f.Carrier := by rw [hf]; omega
  have hl := pslTwo_order_ge_660 ho hb
  have hu := fitting_card_le K hK hm hq
  rw [Nat.card_congr e.toEquiv] at hu
  omega

/-- The field-extension component in row (8) has order at least 360. -/
theorem not_field_extension (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D))
    (r : FieldExtensionRow (D := D)) : False := by
  have hp : 3 ≤ r.field.prime := by have := r.congruence; omega
  have ho : Odd r.field.prime := by rw [Nat.odd_iff]; have := r.congruence; omega
  have hodd : Odd (Nat.card r.field.Carrier) := by rw [r.field.card]; exact ho.pow
  have hb : 9 ≤ Nat.card r.field.Carrier := by
    rw [r.field.card, r.degree]
    nlinarith
  have hl := pslTwo_order_ge_360 hodd hb
  have hu := fitting_card_le K hK hm hq
  rw [Nat.card_congr r.componentEquiv.toEquiv] at hu
  omega

/-- All four degree-three options are excluded by their defining-prime cube. -/
theorem not_degreeThree_component (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D))
    {p : ℕ} (hp : p.Prime) (hc : p % 8 = 3 ∨ p % 8 = 5)
    (h : DegreeThree p (generalizedFitting D)) : False := by
  have hne : p ≠ 2 := by omega
  rcases fitting_small_models K hK hm hq with he | he <;> obtain ⟨e⟩ := he
  · exact degreeThree_not_binaryThree hp hne h e
  · exact degreeThree_not_alternatingFive hp hne h e

/-- The actual M₁₂ component in row (13) also exceeds both small orders. -/
theorem not_mathieu_component (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D))
    (e : generalizedFitting D ≃* Sporadic.Mathieu.M12) : False := by
  have hu := fitting_card_le K hK hm hq
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order] at hu
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First.Evaluations
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Reduction

/-!
# Three conjugates of the first J₄ involution generate the literal model

The packed certificates in `First.Evaluations` establish ga=tg and
ha=(tb)h for explicit words in the actual ATLAS generators. Therefore
⟨a,gag⁻¹,hah⁻¹⟩ contains a, t and tb, hence also b=t⁻¹(tb).
The already certified `closure_a_b` proves generation of the entire carrier.
There is no global order or simplicity premise in this certificate.

This proves the first representative case of Revin--Zavarnitsine,
https://arxiv.org/abs/2505.05173v2, Theorem 1. The matrix and word attribution
and reproducible witness generator are in `First/source/README.md`.
The application to involutory automorphisms discharges the first triple in
`automorphisms_of_representatives`; the second triple remains explicit.
-/

public section
namespace Janko4.ThreeConjugates
open Subgroup Theory.GroupTheory First

/-- The first explicit conjugator sends the standard involution to t. -/
theorem firstG_conjugate : firstG * a * firstG⁻¹ = firstT := by
  rw [firstG_mul_a, mul_inv_cancel_right]

/-- The second explicit conjugator sends the standard involution to tb. -/
theorem firstH_conjugate : firstH * a * firstH⁻¹ = firstT * b := by
  rw [firstH_mul_a, mul_inv_cancel_right]
  rfl

/-- The certified triple recovers both literal ATLAS generators. -/
theorem first_conjugators_generate :
    zpowers a ⊔ zpowers (firstG * a * firstG⁻¹) ⊔
      zpowers (firstH * a * firstH⁻¹) = (⊤ : Subgroup Model) := by
  rw [firstG_conjugate, firstH_conjugate]
  let H : Subgroup Model := zpowers a ⊔ zpowers firstT ⊔ zpowers (firstT * b)
  have ha : a ∈ H := mem_sup_left (mem_sup_left (mem_zpowers a))
  have ht : firstT ∈ H := mem_sup_left (mem_sup_right (mem_zpowers firstT))
  have htb : firstT * b ∈ H := mem_sup_right (mem_zpowers _)
  have hb : b ∈ H := by
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem ht) htb
  change H = ⊤
  apply top_unique
  rw [← closure_a_b, closure_le]
  rintro x (rfl | hx)
  · exact ha
  · rw [Set.mem_singleton_iff.mp hx]
    exact hb

/-- Three actual conjugates of the first involution generate J₄'s matrix carrier. -/
theorem first_three_conjugates_generate : ThreeConjugatesGenerate a :=
  ⟨firstG, firstH, first_conjugators_generate⟩

/-- The first representative's generation premise is discharged; only the second
involution's triple remains for the automorphism-generation assembly. -/
theorem automorphisms_of_second_representative
    [IsSimpleGroup Model] [Group.IsPerfect Model]
    (hsecond : ThreeConjugatesGenerate ((a * b * a * b * b) ^ 5)) :
    ThreeConjugateAutomorphisms Model :=
  automorphisms_of_representatives first_three_conjugates_generate hsecond

end Janko4.ThreeConjugates

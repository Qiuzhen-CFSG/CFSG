module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.SymplecticCoordinates
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Products of binary symplectic root operators

For two isotropic-pair operators, write `t = 1 + A` and `s = 1 + C`.
Their displacements satisfy `A² = C² = 0`, `ACA = λA`, and `CAC = λC`, where
`λ = B(a,c)B(b,d) + B(a,d)B(b,c)`. Over `ZMod 2`, the two possible values of
`λ` give respectively `(ts)⁴ = 1` and `(ts)³ = 1`. Faithfulness then bounds
the order of the original group product by four.

Neither nondegeneracy of the form nor independence of the coordinate pairs
is needed. The construction of these coordinates from intrinsic type `a₂`
is a separate result; the hypotheses here are the explicit normal forms.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof
of 6.2.19, printed p.691 (PDF p.708), and the type convention in Definition
E.2.6, printed p.218 (PDF p.229).
-/

namespace Representation.RankTwo.Symmetric

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (B : LinearMap.BilinForm (ZMod 2) V)

private def displacement (a b : V) : Module.End (ZMod 2) V :=
  (B.flip a).smulRight b + (B.flip b).smulRight a

private lemma displacement_apply (a b x : V) :
    displacement B a b x = B x a • b + B x b • a := rfl

private lemma form_symm (hB : B.IsAlt) (x y : V) : B x y = B y x := by
  simpa only [ZMod.neg_eq_self_mod_two] using hB.neg_eq x y

private lemma displacement_square (hB : B.IsAlt) (a b : V) (hab : B a b = 0) :
    displacement B a b * displacement B a b = 0 := by
  ext x
  have hba : B b a = 0 := (form_symm B hB b a).trans hab
  simp only [Module.End.mul_apply, displacement_apply, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left, hB.self_eq_zero, hab, hba, mul_zero, add_zero,
    zero_smul, LinearMap.zero_apply]

private lemma displacement_triple (hB : B.IsAlt) (a b c d : V) :
    displacement B a b * (displacement B c d * displacement B a b) =
      (B a c * B b d + B a d * B b c) • displacement B a b := by
  ext x
  simp only [Module.End.mul_apply, displacement_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  rw [form_symm B hB c a, form_symm B hB c b,
    form_symm B hB d a, form_symm B hB d b]
  match_scalars <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 from rfl]

private lemma even_zsmul_eq_zero (n : ℤ) (hn : Even n) (x : V) : n • x = 0 := by
  obtain ⟨m, rfl⟩ := hn
  rw [add_smul, ZModModule.add_self]

private lemma product_cube_of_triple_eq_self (A C : Module.End (ZMod 2) V)
    (hA : A * A = 0) (hC : C * C = 0)
    (hACA : A * (C * A) = A) (hCAC : C * (A * C) = C) :
    ((1 + A) * (1 + C)) ^ 3 = 1 := by
  have hAA (X : Module.End (ZMod 2) V) : A * (A * X) = 0 := by
    rw [← mul_assoc, hA, zero_mul]
  have hCC (X : Module.End (ZMod 2) V) : C * (C * X) = 0 := by
    rw [← mul_assoc, hC, zero_mul]
  have hACA' (X : Module.End (ZMod 2) V) : A * (C * (A * X)) = A * X := by
    rw [← mul_assoc C, ← mul_assoc A, hACA]
  noncomm_ring [hA, hC, hACA, hCAC, hAA, hCC, hACA']
  simp (discharger := decide) only [even_zsmul_eq_zero, add_zero]

private lemma product_fourth_of_triple_eq_zero (A C : Module.End (ZMod 2) V)
    (hA : A * A = 0) (hC : C * C = 0)
    (hACA : A * (C * A) = 0) (hCAC : C * (A * C) = 0) :
    ((1 + A) * (1 + C)) ^ 4 = 1 := by
  have hAA (X : Module.End (ZMod 2) V) : A * (A * X) = 0 := by
    rw [← mul_assoc, hA, zero_mul]
  have hCC (X : Module.End (ZMod 2) V) : C * (C * X) = 0 := by
    rw [← mul_assoc, hC, zero_mul]
  have hACA' (X : Module.End (ZMod 2) V) : A * (C * (A * X)) = 0 := by
    rw [← mul_assoc C, ← mul_assoc A, hACA, zero_mul]
  have hCAC' (X : Module.End (ZMod 2) V) : C * (A * (C * X)) = 0 := by
    rw [← mul_assoc A, ← mul_assoc C, hCAC, zero_mul]
  noncomm_ring [hA, hC, hACA, hCAC, hAA, hCC, hACA', hCAC']
  simp (discharger := decide) only [even_zsmul_eq_zero, add_zero]

/-- The product of two operators in binary symplectic root coordinates has
its cube or its fourth power equal to the identity. -/
public theorem HasA2NormalForm.mul_pow_three_or_four {t s : Module.End (ZMod 2) V}
    (hB : B.IsAlt) (ht : HasA2NormalForm B t) (hs : HasA2NormalForm B s) :
    (t * s) ^ 3 = 1 ∨ (t * s) ^ 4 = 1 := by
  obtain ⟨a, b, hab, ht⟩ := ht
  obtain ⟨c, d, hcd, hs⟩ := hs
  have ht' : t = 1 + displacement B a b := by
    ext x
    simpa only [LinearMap.add_apply, Module.End.one_apply, displacement_apply, add_assoc]
      using ht x
  have hs' : s = 1 + displacement B c d := by
    ext x
    simpa only [LinearMap.add_apply, Module.End.one_apply, displacement_apply, add_assoc]
      using hs x
  rw [ht', hs']
  have hA := displacement_square B hB a b hab
  have hC := displacement_square B hB c d hcd
  have hACA := displacement_triple B hB a b c d
  have hCAC := displacement_triple B hB c d a b
  have hsym : B c a * B d b + B c b * B d a = B a c * B b d + B a d * B b c := by
    rw [form_symm B hB c a, form_symm B hB d b,
      form_symm B hB c b, form_symm B hB d a]
    ring
  rw [hsym] at hCAC
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary (B a c * B b d + B a d * B b c) with hzero | hone
  · right
    simp only [hzero, zero_smul] at hACA hCAC
    exact product_fourth_of_triple_eq_zero _ _ hA hC hACA hCAC
  · left
    simp only [hone, one_smul] at hACA hCAC
    exact product_cube_of_triple_eq_self _ _ hA hC hACA hCAC

/-- Faithfulness transfers the coordinate calculation to the actual group
product. This discharges the product-order bound used in the proof of 6.2.19
once the two normal forms have been constructed. -/
public theorem orderOf_mul_le_four_of_normal_forms {G : Type*} [Group G]
    (hB : B.IsAlt) (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {v w : G} (hv : HasA2NormalForm B (ρ v)) (hw : HasA2NormalForm B (ρ w)) :
    orderOf (v * w) ≤ 4 := by
  rw [← orderOf_injective ρ hρ (v * w), map_mul]
  rcases HasA2NormalForm.mul_pow_three_or_four B hB hv hw with hthree | hfour
  · exact (orderOf_le_of_pow_eq_one (by decide) hthree).trans (by decide)
  · exact orderOf_le_of_pow_eq_one (by decide) hfour

end Representation.RankTwo.Symmetric

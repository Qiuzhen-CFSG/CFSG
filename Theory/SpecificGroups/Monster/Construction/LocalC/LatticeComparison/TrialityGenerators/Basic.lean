module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.GeneratorCoordinates
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CoordinateMap
public import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
# Actual conjugation on the first triality subgroup

Relative normality of `Q1` in `N1` restricts the actual permutation conjugation
`g * q * g⁻¹` to automorphisms of `Q1`. Its coordinates are unchanged for inner
conjugation by `Q1`, because the proved coordinate homomorphism has abelian
image. In particular this handles the first loop-generator family.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.6 and Lemma 27.2,
printed pp. 64, 144–145; the comparison on p. 148. Lean products use left
composition, reversing the source right-action products.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- Restriction of permutation conjugation to the relatively normal subgroup. -/
def q1Conjugation : N1 →* MulAut Q1 where
  toFun g :=
    { toFun q := ⟨g.val * q.val * g.val⁻¹,
        Q1_normal_in_N1.conj_mem (⟨q.val, Q1_le_N1 q.prop⟩ : N1) q.prop g⟩
      invFun q := ⟨g.val⁻¹ * q.val * g.val,
        by
          have h := Q1_normal_in_N1.conj_mem
            (⟨q.val, Q1_le_N1 q.prop⟩ : N1) q.prop g⁻¹
          change g.val⁻¹ * q.val * (g.val⁻¹)⁻¹ ∈ Q1 at h
          simpa only [inv_inv] using h⟩
      left_inv q := by apply Subtype.ext; simp [mul_assoc]
      right_inv q := by apply Subtype.ext; simp [mul_assoc]
      map_mul' q r := by apply Subtype.ext; simp [mul_assoc] }
  map_one' := by apply MulEquiv.ext; intro q; apply Subtype.ext; simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    change (g.val * h.val) * q.val * (g.val * h.val)⁻¹ = _
    simp [mul_assoc]

@[simp] theorem q1Conjugation_val (g : N1) (q : Q1) :
    (q1Conjugation g q).val = g.val * q.val * g.val⁻¹ := rfl

/-- Inner conjugations disappear in the abelian coordinate quotient. -/
theorem q1Coordinates_conjugation_of_mem (g : Q1) (q : Q1) :
    q1Coordinates (q1Conjugation ⟨g.val, Q1_le_N1 g.prop⟩ q) = q1Coordinates q := by
  have h : q1Conjugation ⟨g.val, Q1_le_N1 g.prop⟩ q = g * q * g⁻¹ := rfl
  rw [h, map_mul, map_mul, map_inv]
  simp

/-- Exercise 4.6(4): the first Parker family fixes every coordinate. -/
theorem q1Coordinates_conjugation_psi1 (d : ParkerLoop) (q : Q1) :
    (q1Coordinates (q1Conjugation ⟨psi1N d, psi1N_mem_N1 d⟩ q)).toAdd =
      (q1Coordinates q).toAdd := by
  exact congrArg Multiplicative.toAdd
    (q1Coordinates_conjugation_of_mem
      ⟨psi1N d, Subgroup.subset_closure (Or.inl ⟨d,rfl⟩)⟩ q)

end Sporadic.Monster.Construction.LocalC

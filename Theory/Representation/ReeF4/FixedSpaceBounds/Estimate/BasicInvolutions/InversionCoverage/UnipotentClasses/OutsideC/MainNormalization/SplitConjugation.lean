module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization.Split0
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization.Split1
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization.Split2
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization.Split3

/-!
# Conjugation by the first B₂ block

Compose four checked split-root conjugations. Only the eighth coordinate and
the two main coordinates are retained; all other coordinates exist by the
same literal collection. This is used to normalize the actual Ree word.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalizationCalculation
open Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination

attribute [local irreducible] X

/-- The three required coordinates after conjugation by an arbitrary first B₂ block. -/
theorem split_firstBlock_conjugate (m : ℕ) (v : Fin 24 → CoefficientField m)
    (a b c d : CoefficientField m) (h0 : v 0 = 0) (h1 : v 1 = 0)
    (h2 : v 2 = 0) (h3 : v 3 = 0) :
    ∃ w : Fin 24 → CoefficientField m,
      (X m 0 a * X m 1 b * X m 2 c * X m 3 d) * splitWord m v *
        (X m 0 a * X m 1 b * X m 2 c * X m 3 d)⁻¹ = splitWord m w ∧
      w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 22 = v 22 ∧
      w 18 = a * v 22 + v 18 ∧ w 6 = b ^ 2 * v 18 + d * v 22 + v 6 := by
  obtain ⟨v3, e3, h30, h31, h32, h33, h322, h318, h36⟩ :=
    split_conjugate_3 m v d h0 h1 h2 h3
  obtain ⟨v2, e2, h20, h21, h22, h23, h222, h218, h26⟩ :=
    split_conjugate_2 m v3 c h30 h31 h32 h33
  obtain ⟨v1, e1, h10, h11, h12, h13, h122, h118, h16⟩ :=
    split_conjugate_1 m v2 b h20 h21 h22 h23
  obtain ⟨w, e0, hw0, hw1, hw2, hw3, hw22, hw18, hw6⟩ :=
    split_conjugate_0 m v1 a h10 h11 h12 h13
  refine ⟨w, ?_, hw0, hw1, hw2, hw3, ?_, ?_, ?_⟩
  · calc
      _ = X m 0 a * (X m 1 b * (X m 2 c *
            (X m 3 d * splitWord m v * X m 3 d) * X m 2 c) * X m 1 b) * X m 0 a := by
          simp only [mul_inv_rev, xi, mul_assoc]
      _ = splitWord m w := by rw [e3, e2, e1, e0]
  · exact hw22.trans (h122.trans (h222.trans h322))
  · simpa only [h118, h218, h318, h122, h222, h322, add_comm] using hw18
  · simpa only [h16, h26, h36, h218, h318, mul_comm, add_assoc, add_comm, add_left_comm] using hw6

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalizationCalculation

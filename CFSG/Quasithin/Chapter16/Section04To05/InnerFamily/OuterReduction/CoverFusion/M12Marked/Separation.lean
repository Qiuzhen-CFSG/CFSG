module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Separating M₁₂ from the exceptional large-center quotients

The actual orders of M₁₂, Sz(8), PSL₃(4), and M₂₂ distinguish the models.
For PSL₃(4), the argument uses the order formula over the field supplied by
the model witness, rather than identifying an arbitrary field by name.

This specializes the complete center alternative of 16.1.2(2) in the M₁₂
case of the proof of 16.4.9(2): Aschbacher–Smith, combined manuscript of
1 March 2004, printed pp.1170 and 1191.
-/

public section
open Subgroup Sporadic.Mathieu BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion

/-- The concrete M₁₂ quotient permits none of the three large-center cases. -/
theorem m12_excludesLargeCenterQuotients : ExcludesLargeCenterQuotients M12 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [m12_order, suzukiMatrixGroup_card 1 (by decide)] at h
    norm_num at h
  · rintro ⟨F, hF, hf, hcard, ⟨e⟩⟩
    have h := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
    rw [hcard, ← Nat.card_congr e.toEquiv, m12_order] at h
    norm_num at h
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [m12_order, m22_order] at h
    norm_num at h

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion

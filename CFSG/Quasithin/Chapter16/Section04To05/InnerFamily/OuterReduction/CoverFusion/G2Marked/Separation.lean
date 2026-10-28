module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.Mathieu.M22.Properties.Order

/-!
# Separating the G₂(4) quotient from the large-center exceptions

The established orders of the actual octonion, Suzuki, projective matrix and
Mathieu carriers exclude each isomorphism in the large-center alternatives
of 16.1.2(2). No recognition theorem or simplicity certificate is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2(2), printed p.1170, and the double-cover argument on p.1191.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked
variable {F : Type*} [Field F] [Finite F]

/-- The established order formula specialized to the actual G₂(4) carrier. -/
theorem card_model (hF : Nat.card F = 4) : Nat.card (Atlas.G2.Model F) = 251596800 := by
  rw [Atlas.G2.card_Model, hF]
  norm_num

/-- None of the three exceptional large-center quotients is G₂(4). -/
theorem excludesLargeCenterQuotients (hF : Nat.card F = 4) :
    ExcludesLargeCenterQuotients (Atlas.G2.Model F) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toEquiv
    rw [card_model hF, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)] at hc
    norm_num at hc
  · rintro ⟨K, hK, hfin, hq, ⟨e⟩⟩
    have hc := Nat.card_congr e.toEquiv
    rw [card_model hF, Matrix.PSL3.LinearThree.card_projective, hq] at hc
    norm_num at hc
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toEquiv
    rw [card_model hF, Sporadic.Mathieu.m22_order] at hc
    norm_num at hc

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked

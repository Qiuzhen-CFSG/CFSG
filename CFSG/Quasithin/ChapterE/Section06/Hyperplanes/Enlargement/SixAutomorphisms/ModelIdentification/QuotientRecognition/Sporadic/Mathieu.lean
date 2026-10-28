module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Reduction
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M12.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders

/-!
# Mathieu fixed-order tests in the six-component enlargement

The actual involutory automorphism fixed-order calculations bound the M₁₂
fixed group by 297 and exclude nine as a divisor for M₂₂. Hence neither fixed
group can contain A₆, whose order is 360. The source application uses the original quotient and its induced actor.

Source: Aschbacher–Smith E.6.23, printed p.254 (PDF p.265).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
open _root_.Sporadic.Mathieu

/-- The concrete M₂₂ fixed-order theorem excludes every involution-fixed A₆ component. -/
theorem m22 : FixedSixExclusion M22 :=
  FixedSixExclusion.of_fixed_card m22_involution_not_360_dvd_fixed_card

/-- Apply the proved M₂₂ model calculation to the literal source quotient Y/Z(Y). -/
theorem m22_source {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion M22 T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => m22) T M V

/-- The certified M₁₂ conjugacy-class bounds exclude every fixed A₆ component. -/
theorem m12 : FixedSixExclusion M12 :=
  FixedSixExclusion.of_fixed_card m12_involution_not_360_dvd_fixed_card

/-- Apply the complete M₁₂ order calculation to the literal quotient and actor. -/
theorem m12_source {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion M12 T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => m12) T M V

/- The concrete M₂₄ fixed-order theorem likewise excludes a fixed A₆. -/
theorem m24 : FixedSixExclusion M24 :=
  FixedSixExclusion.of_fixed_card m24_involution_not_360_dvd_fixed_card

theorem m24_source {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion M24 T M V :=
  sourceExclusion_of_fixed_exclusion (fun _ _ => m24) T M V

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic

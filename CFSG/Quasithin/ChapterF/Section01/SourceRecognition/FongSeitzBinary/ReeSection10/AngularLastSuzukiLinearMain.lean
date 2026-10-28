module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinearTransfer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinearTorus
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.EndpointCoefficientRigidity

/-!
# The last Suzuki-linear source equation

The transferred parameter-one seed satisfies the native reflection, square and
adjacent-commutation constraints. Native endpoint rigidity fixes all five
remaining coefficients, and the synchronized torus characters extend that
seed to every pair of field parameters.

Source: Fong--Seitz II, Section 10, (10.27)--(10.41).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)

/-- The native rigidity calculation fixes the transferred parameter-one seed. -/
theorem synchronizedSuzukiLinear_seed :
    (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 1 * L 2 1 * S 1 0 1 * L 3 1 * S 3 1 0 * L 1 1 := by
  obtain ⟨s,e,t,v,w,hk,hV,hsq,hco⟩ :=
    synchronizedSuzukiLinear_seed_native_data Q split c
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ :=
    EndpointCoefficientRigidity.endpoint_coefficients m s e t v w hV hsq hco
  exact hk

/-- The last Suzuki-linear commutator for all field parameters. -/
theorem synchronized_last_main_commutator (a x : CoefficientField m) :
    (L 0 x)⁻¹ * (S 0 a 0)⁻¹ * L 0 x * S 0 a 0 =
      S 2 (a*x) (titsEnd m (a*x)*(a*x)) *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 3 ((a*titsEnd m a)*x) 0 * L 1 ((a^2*titsEnd m a)*x) :=
  synchronized_last_main_commutator_of_seed Q split c
    (synchronizedSuzukiLinear_seed Q split c) a x

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

module
public import Theory.SpecificGroups.PrimeToFifteen.Exceptional.RootPair
/-!
# Three-divisibility of all split exceptional carriers

One positive and one negative simple root already force a cubic element in
 the literal central quotient. The argument holds over every field and does
not need an order formula or a simplicity certificate.
Source: Steinberg's rank-one relations, GLS3 Sections 2.1–2.3.
-/
public section
open Matrix RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
namespace ExceptionalSplit
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]
theorem model_three_dvd_card (i : b.support) : 3 ∣ Nat.card (Model P b F) := by
  apply RootPairing.SimpleGeckGroup.ThreeDivisibility.three_dvd_subgroup_center_quotient
    (rootGenerated P b F) i
  · simpa only [rootCurveUnit_simple] using root_mem P b F (i : ι) 1
  · let := P.indexNeg
    simpa only [rootCurveUnit_neg_simple] using root_mem P b F (-i : ι) (-1)

attribute [local instance] Classical.decEq
private instance : Fintype typeF4Roots := Fintype.ofFinite _
private instance : Fintype typeE6Roots := Fintype.ofFinite _
private instance : Fintype typeE7Roots := Fintype.ofFinite _
private instance : Fintype typeE8Roots := Fintype.ofFinite _
theorem f4_three_dvd_card (F : Type*) [Field F] : 3 ∣ Nat.card (F4 F) :=
  model_three_dvd_card (typeF4RootPairing_baseEquiv 0)
theorem e6_three_dvd_card (F : Type*) [Field F] : 3 ∣ Nat.card (E6 F) :=
  model_three_dvd_card (typeE6RootPairing_baseEquiv 0)
theorem e7_three_dvd_card (F : Type*) [Field F] : 3 ∣ Nat.card (E7 F) :=
  model_three_dvd_card (typeE7RootPairing_baseEquiv 0)
theorem e8_three_dvd_card (F : Type*) [Field F] : 3 ∣ Nat.card (E8 F) :=
  model_three_dvd_card (typeE8RootPairing_baseEquiv 0)
end ExceptionalSplit

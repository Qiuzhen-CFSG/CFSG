module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiNear

/-!
# The native opposite Suzuki main-curve commutator

The checked split-root calculation fixes the opposite main-curve relation in
the same right-commutator convention as the source coordinates. Reversing the
commutator reverses its three factors and retains the inverse on the first
Suzuki factor. Its central coordinate is therefore generally nonzero, also
over the binary field.

Source: GLS3 Table 2.4 and 2.4.5(d); Fong--Seitz II, Section 10,
(10.23)--(10.26), with the literal native chart convention.
-/

@[expose] public noncomputable section
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularSuzukiOpposite
open CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators
open Parabolics.RadicalCoordinates.FixedCoordinates
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private theorem main_eq (i : Fin 4) (a : CoefficientField m) :
    S i a 0 = mainElement m (![0,4,6,2] i) a := by
  rw [PositiveTables.quartet_blockPoint, blockPoint, centralElement_zero, mul_one]
  simp only [rootIndex, positive_quartet_indices]
  rfl

private theorem pair_eq (i : Fin 4) (a : CoefficientField m) :
    L i a = mainElement m (![7,1,5,3] i) a := by
  rw [PositiveTables.pair_main]
  simp only [rootIndex, positive_pair_indices]
  rfl

private theorem linear_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul]
  simp only [CharTwo.add_self_eq_zero,PositiveTables.pair_zero,Subgroup.coe_one]

/-- The native right commutator in the source's opposite-first convention. -/
theorem main_right_commutator (a y : CoefficientField m) :
    (S 2 y 0)⁻¹ * (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
      (S 1 (a*titsEnd m y) 0)⁻¹ *
        L 3 ((a*titsEnd m a)*(y*titsEnd m y)) * S 3 (titsEnd m a*y) 0 := by
  have h : (S 0 a 0)⁻¹ * (S 2 y 0)⁻¹ * S 0 a 0 * S 2 y 0 =
      (S 3 (titsEnd m a*y) 0)⁻¹ *
        L 3 ((a*titsEnd m a)*(y*titsEnd m y)) * S 1 (a*titsEnd m y) 0 := by
    rw [main_eq,main_eq,main_eq,main_eq,pair_eq]
    exact Subtype.ext (rootWord_first_seventh_commutator m a y)
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev,inv_inv,linear_inv,mul_assoc] using hi

/-- In native chart coordinates the inverse contributes its Suzuki cocycle. -/
theorem main_right_coordinates (a y : CoefficientField m) :
    (S 2 y 0)⁻¹ * (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
      S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) *
        L 3 ((a*titsEnd m a)*(y*titsEnd m y)) * S 3 (titsEnd m a*y) 0 := by
  rw [main_right_commutator]
  have hi (i : Fin 4) (t : CoefficientField m) :
      (S i t 0)⁻¹ = S i t (titsEnd m t*t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
    simp only [zero_add,CharTwo.add_self_eq_zero,PositiveTables.quartet_zero,
      Subgroup.coe_one]
  rw [hi]

end ReeF4.RootPresentationRecognition.AngularSuzukiOpposite

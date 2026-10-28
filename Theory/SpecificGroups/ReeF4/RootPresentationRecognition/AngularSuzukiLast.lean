module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiOpposite

/-!
# The native last Suzuki-linear main-curve commutator

Reversing the checked first-eighth right commutator gives the source's
linear-first convention. The inverse first Suzuki factor contributes its
native central coordinate. All six factors are retained in reverse angular
order, so this identity can be transported by the seven-root realization.

Source: GLS3 Table 2.4 and 2.4.5(d); Fong--Seitz II (1974), Section 10,
(10.27)--(10.41), in the literal native triangular chart.
-/

@[expose] public noncomputable section
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularSuzukiLast
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
  rw [PositiveTables.quartet_blockPoint,blockPoint,centralElement_zero,mul_one]
  simp only [rootIndex,positive_quartet_indices]
  rfl

private theorem omega_eq (i : Fin 4) (b : CoefficientField m) :
    S i 0 b = centralElement m (![0,4,6,2] i) b := by
  rw [PositiveTables.quartet_blockPoint,blockPoint,mainElement_zero,one_mul]
  simp only [rootIndex,positive_quartet_indices]
  rfl

private theorem pair_eq (i : Fin 4) (a : CoefficientField m) :
    L i a = mainElement m (![7,1,5,3] i) a := by
  rw [PositiveTables.pair_main]
  simp only [rootIndex,positive_pair_indices]
  rfl

private theorem linear_inv (i : Fin 4) (a : CoefficientField m) :
    (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul]
  simp only [CharTwo.add_self_eq_zero,PositiveTables.pair_zero,Subgroup.coe_one]

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) :
    (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
  simp only [map_zero,zero_mul,CharTwo.add_self_eq_zero,
    PositiveTables.quartet_zero,Subgroup.coe_one]

/-- The native right commutator in the source's linear-first convention. -/
theorem main_right_commutator (a x : CoefficientField m) :
    (L 0 x)⁻¹ * (S 0 a 0)⁻¹ * L 0 x * S 0 a 0 =
      (S 2 (a*x) 0)⁻¹ *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 3 ((a*titsEnd m a)*x) 0 * L 1 ((a^2*titsEnd m a)*x) := by
  have h : (S 0 a 0)⁻¹ * (L 0 x)⁻¹ * S 0 a 0 * L 0 x =
      L 1 ((a^2*titsEnd m a)*x) * (S 3 ((a*titsEnd m a)*x) 0)⁻¹ *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) * S 2 (a*x) 0 := by
    rw [main_eq,pair_eq,pair_eq,main_eq,pair_eq,omega_eq,pair_eq,main_eq]
    exact Subtype.ext (rootWord_first_eighth_commutator m a x)
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev,inv_inv,linear_inv,omega_inv,mul_assoc] using hi

/-- The inverse Suzuki factor in the native chart has its cocycle coordinate. -/
theorem main_right_coordinates (a x : CoefficientField m) :
    (L 0 x)⁻¹ * (S 0 a 0)⁻¹ * L 0 x * S 0 a 0 =
      S 2 (a*x) (titsEnd m (a*x)*(a*x)) *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 3 ((a*titsEnd m a)*x) 0 * L 1 ((a^2*titsEnd m a)*x) := by
  rw [main_right_commutator]
  have hi (i : Fin 4) (t : CoefficientField m) :
      (S i t 0)⁻¹ = S i t (titsEnd m t*t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
    simp only [zero_add,CharTwo.add_self_eq_zero,PositiveTables.quartet_zero,
      Subgroup.coe_one]
  rw [hi]

end ReeF4.RootPresentationRecognition.AngularSuzukiLast

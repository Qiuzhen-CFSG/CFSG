module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.PushingUp
public import Theory.SpecificGroups.FivePointSylowParabolic

/-!
# Minimal parabolicity of the fixed five-point join

The literal map from K C_T(u) to S₅ has two-group kernel and contains A₅ in
its range. The five-point Sylow overgroup theorem supplies both the unique
maximal overgroup and nonnormality required by Definition B.6.1. This removes
exactly the minimal-parabolic premise of the C.1.26 deduction. The earlier
commutator identities, maximal two-local hypothesis, and full C.1.26 input
remain explicit for the parent source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.6.1, p.112; C.1.26, p.132; proof of 14.7.68(2), pp.1071–1072.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin

/-- Two-group extensions of five-point groups containing A₅ are minimal
parabolics over every Sylow two-subgroup. -/
theorem ChapterB.isMinimalParabolicOver_of_five_point_map
    {E : Type*} [Group E] [Finite E] (f : E →* ChapterJ.S5)
    (hker : IsPGroup 2 f.ker) (hA : alternatingGroup (Fin 5) ≤ f.range)
    (P : Sylow 2 E) : ChapterB.IsMinimalParabolicOver P ⊤ :=
  (ChapterB.isMinimalParabolicOver_top_iff P).mpr
    (Theory.SpecificGroups.FivePointSylowParabolic.unique_maximal_of_five_point_map f hker hA P)

namespace Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The actual K C_T(u) is minimal parabolic; the prescribed fixed Sylow
embedding is not needed for this stronger all-Sylows assertion. -/
theorem fixedJoin_minimalParabolic (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) (P : Sylow 2 (d.fixedJoin u)) :
    ChapterB.IsMinimalParabolicOver P ⊤ := by
  apply ChapterB.isMinimalParabolicOver_of_five_point_map (d.fixedJoinMap u)
  · rw [d.fixedJoinMap_ker u hu hfix]
    exact pCore_isPGroup
  · exact d.alternating_le_fixedJoinMap_range u

/-- Apply the full C.1.26 source implication with its minimal-parabolic
hypothesis now proved from the literal five-point quotient. -/
theorem fixedCharacteristic_of_C126_fivePoint
    (choices : DistinguishedPairs.{u})
    (source : C126Source KnownSimple.IsKnownSimple choices)
    (hUK : ⁅F.U, K F⁆ = F.U) (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    Nonempty (d.FixedCharacteristicWitness u) :=
  d.fixedCharacteristic_of_C126 choices source hUK hUQ u hu hne hfix hmax
    (fun P _ => d.fixedJoin_minimalParabolic u hu hfix P)

end Data
end Chapter14.Section07.LocalStructure.CriticalFusion.Source
end CFSG.Quasithin

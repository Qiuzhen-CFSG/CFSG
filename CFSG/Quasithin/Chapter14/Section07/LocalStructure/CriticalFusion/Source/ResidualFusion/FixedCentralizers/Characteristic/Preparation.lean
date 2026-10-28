module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.PentadParabolic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator

/-!
# Characteristic preparation with the original natural seed

The original natural L₃(2) marking proves U = [U,K]. Together with the
earlier 14.5.21(2) point-commutator identity, this excludes shortness of K.
The literal five-point quotient proves minimal parabolicity of K C_T(u),
so the full C.1.26 implication constructs a nonidentity characteristic
subgroup of the actual C_T(u), normal relative to K C_T(u). Its normalizer
then promotes C_T(u) to a Sylow subgroup of C_G(u).

Only the full C.1.26 input (qt-c-01) and the point-commutator identity
(qt-14-05-terminal-duality) remain explicit. In particular neither
minimal parabolicity nor U = [U,K] is assumed. The containing component's
odd alternatives are a separate, still necessary step of 14.7.68(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21(2), pp.1019–1020; 14.7.48(2), p.1064; 14.7.68(2), p.1071;
C.1.26, p.132.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

include d in
/-- The natural seed discharges the K-generation premise in the non-short argument. -/
theorem K_not_short_of_point_commutator
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : ¬ ChapterC.IsShort (K F) :=
  d.K_not_short_of_source_commutators d.U_eq_commutator_K.symm hUQ

/-- C.1.26 constructs the witness on the original fixed Sylow. All of its local
SQTK, characteristic-two and minimal-parabolic hypotheses are proved. -/
theorem fixedCharacteristic_of_point_commutator
    (choices : DistinguishedPairs.{u})
    (source : C126Source KnownSimple.IsKnownSimple choices)
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    Nonempty (d.FixedCharacteristicWitness u) :=
  d.fixedCharacteristic_of_C126_fivePoint choices source d.U_eq_commutator_K.symm
    hUQ u hu hne hfix hmax

/-- The constructed witness discharges the fixed-centralizer component
assembly's Sylow premise; no characteristic subgroup is assumed here. -/
theorem fixedSylow_isSylow_of_point_commutator
    (choices : DistinguishedPairs.{u})
    (source : C126Source KnownSimple.IsKnownSimple choices)
    (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H) :
    Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u) := by
  obtain ⟨w⟩ := d.fixedCharacteristic_of_point_commutator choices source hUQ u hu hne hfix hmax
  exact w.fixedSylow_isSylow hu hfix hmax

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

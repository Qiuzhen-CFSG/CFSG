module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.GroupTheory.TwoPerfectSylowAction

/-!
# Solvable Sylow control in the original natural layer

The existing nonbinary matrix and root calculations control solvable Sylow
overgroups in all three natural models. The linear calculation is lifted
through the full scalar center, so its input and output are SL₃, not PSL₃.
Transport through the original marking then gives control in the literal
image of L on V, including nonsplit central attachments to V.

Source: Aschbacher--Smith A.3.15(5) and 11.2.1, pp.50--51,766--767.
This is the model placement step; the automizer exponent calculation remains
with the weak-closure source owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer

/-- Solvable Sylow control on full SL₃, preserving its scalar center. -/
theorem sl3_solvable_sylow_control (F : BinaryField) (hn : 1 < F.degree) :
    SolvableSylowControl 2 (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  apply SolvableSylowControl.of_surjective_central_kernel
    (Matrix.PSL3.projection F.Carrier)
    (Matrix.PSL3.projection_surjective F.Carrier)
  · rw [Matrix.PSL3.projection_ker]
  · exact Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F.Carrier hn F.card_eq

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- All three literal models have solvable Sylow control over the given field. -/
theorem model_solvable_sylow_control (c : Coordinates D S.field) :
    SolvableSylowControl 2 c.ModelGroup := by
  cases c with
  | sl3 m => exact sl3_solvable_sylow_control S.field S.nonbinary
  | sp4 m =>
    exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits
      S.field.card_eq S.nonbinary
      (Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal
        (by rw [S.field.card_eq]
            exact (show 2 ^ 1 < 2 ^ S.field.degree from
              Nat.pow_lt_pow_right (by decide) S.nonbinary)))
  | g2 m =>
    apply SolvableSylowControl.of_standard Atlas.G2.LieParabolicSetup.sylow Atlas.G2.borel
    · exact Atlas.G2.SylowNormalizer.normalizer_unipotent
    · intro A hsol hU
      apply Atlas.G2.SolvableSylowPlacement.le_borel _ A hU hsol
      rw [S.field.card_eq]
      exact (show 2 ^ 1 < 2 ^ S.field.degree from
        Nat.pow_lt_pow_right (by decide) S.nonbinary)

/-- Control transports through the faithful action of the original L/O₂(L). -/
theorem layer_solvable_sylow_control (c : Coordinates D S.field) :
    SolvableSylowControl 2 (inducedAutomizer V L) :=
  SolvableSylowControl.of_equiv (Parameters.FullAutomizer.layerEquiv D S c)
    (model_solvable_sylow_control D S c)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer

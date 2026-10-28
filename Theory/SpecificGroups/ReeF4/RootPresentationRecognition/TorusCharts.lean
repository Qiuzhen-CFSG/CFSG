module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceBorel
import all Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.TorusSeparation
/-!
# Torus characters on all positive Ree root charts

The fixed diagonal torus acts on each linear root by its long-root character
and on each whole Suzuki root by that character and its Tits norm. The eight
characters are evaluated in the two simple-root parameters. This is the
native coefficient calculation used to compare source torus actions.

The implementation-only import reuses the checked matrix conjugation proof
from `TorusSeparation`; no private declaration occurs in this public API.
Source: GLS3 Table 2.4 and Theorem 2.4.7(f).
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.TorusCharts
open Subgroup Parabolics CentralCovers.TwoPrimary CentralCovers.OddPrimary.Order
open LocalBlockInput.PairRigidity.BlockParameters
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open TailRelations.TorusSeparation
variable {m : ℕ}

def character (t : TorusParameter m) (i : PositiveTables.Root) : (CoefficientField m)ˣ :=
  rootScale (blockTorus t.1 t.2) (longRoot (rootIndex i))

private theorem torus_matrix (t : TorusParameter m) :
    matrixRepresentation m (torus m t) = (torusMatrix (blockTorus t.1 t.2))⁻¹ := by
  have h : ((toSplitGroup m) (torus m t)).val =
      (torusMatrix (blockTorus t.1 t.2))⁻¹ :=
    ConverseParabolics.FullLeviRepresentation.torusElement_matrix t.1 t.2
  simpa only [toSplitGroup_apply, matrixRepresentation_apply] using h

theorem pair_action (t : TorusParameter m) (i : Fin 4) (x : CoefficientField m) :
    SourceBorel.rootAction (fixedTorusEquiv m t) (.inl i)
      (PositiveTables.rootChartEquiv m (.inl i) x) =
      PositiveTables.rootChartEquiv m (.inl i) ((character t (.inl i) : CoefficientField m)*x) := by
  apply Subtype.ext
  change torus m t * (PositiveTables.pair m i x : Model m) * (torus m t)⁻¹ =
    PositiveTables.pair m i ((character t (.inl i) : CoefficientField m)*x)
  simp only [PositiveTables.pair_main]
  exact conj_main _ (blockTorus_twistCompatible _ _) _ (torus_matrix t) _ x

theorem quartet_action (t : TorusParameter m) (i : Fin 4) (x y : CoefficientField m) :
    SourceBorel.rootAction (fixedTorusEquiv m t) (.inr i)
      (PositiveTables.rootChartEquiv m (.inr i) (x,y)) =
      PositiveTables.rootChartEquiv m (.inr i)
        ((character t (.inr i) : CoefficientField m)*x,
          (character t (.inr i) : CoefficientField m)*titsEnd m (character t (.inr i))*y) := by
  apply Subtype.ext
  change torus m t * (PositiveTables.quartet m i x y : Model m) * (torus m t)⁻¹ =
    PositiveTables.quartet m i ((character t (.inr i) : CoefficientField m)*x)
      ((character t (.inr i) : CoefficientField m)*titsEnd m (character t (.inr i))*y)
  simp only [PositiveTables.quartet_blockPoint]
  have h := conj_blockPoint _ (blockTorus_twistCompatible t.1 t.2) _ (torus_matrix t)
    (rootIndex (.inr i)) (positiveRootWordLayout.quartet_even i) x y
  simpa only [character,centralScale,Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_map,
    MonoidHom.coe_coe,theta_sq] using h

theorem character_pair (t : TorusParameter m) (i : Fin 4) :
    character t (.inl i) =
      ![t.1,t.1*t.2^(2+2*2^m),t.1^(1+2*2^m)*t.2^(2+2*2^m),
        t.1^(1+2*2^m)*t.2^(2+4*2^m)] i := by
  rw [character,blockTorus_long_scale]
  dsimp only [rootIndex, Sum.elim]
  rw [positive_pair_indices]
  fin_cases i <;> simp [weightA,weightB] <;> norm_cast

theorem character_quartet (t : TorusParameter m) (i : Fin 4) :
    character t (.inr i) =
      ![t.2,t.1^(2*2^m)*t.2^(1+2*2^m),t.1*t.2,t.1*t.2^(1+2*2^m)] i := by
  rw [character,blockTorus_long_scale]
  dsimp only [rootIndex, Sum.elim]
  rw [positive_quartet_indices]
  fin_cases i <;> simp [weightA,weightB] <;> norm_cast
end ReeF4.RootPresentationRecognition.TorusCharts

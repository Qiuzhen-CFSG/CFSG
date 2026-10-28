module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer.SingleOrbit.FiniteCertificate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.WordAction

/-!
# Actual conjugates of the original max2 plane word

The finite certificate contains 1386 distinct masks reachable from 6607.
An action edge by g extends a left conjugator w to g⁻¹w. The certified
injectivity of the original kernel products therefore turns the mask
certificate into distinct actual conjugates. The structural word-collection
theorem discharges the original-word arithmetic law.

Source: ATLAS J4G1-max2W1, with provenance in TwoCoreCentralizer/source;
Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith A.3.12, pp.47--48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open PairOrbitData SingleOrbitData

attribute [local irreducible] kernelProduct

private theorem source_action_step (ha : SourceActionLaw)
    (s : Bool) (m n : Fin 8192) (h : maskAction s m.val = n.val) :
    (sourceGenerator s)⁻¹ * kernelProduct m * sourceGenerator s = kernelProduct n := by
  calc
    _ = maskProduct kernelFactor (maskAction s m.val) := ha s m
    _ = maskProduct kernelFactor n.val := congrArg (maskProduct kernelFactor) h
    _ = kernelProduct n := by unfold kernelProduct; rfl

/-- A finite mask path realizes an actual conjugate of the original max2 word. -/
theorem reachable_realize (ha : SourceActionLaw) {m : Fin 8192} (h : Reachable m) :
    ∃ w : sourceSubgroup, (MulAut.conj w) sourceP = kernelProduct m := by
  induction h with
  | root =>
    refine ⟨1, ?_⟩
    simp only [MulAut.conj_apply, one_mul, inv_one, mul_one, sourceP]
  | @step m n s hm he ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(sourceGenerator s)⁻¹ * w, ?_⟩
    calc
      _ = (sourceGenerator s)⁻¹ * ((MulAut.conj w) sourceP) * sourceGenerator s := by
        simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
      _ = (sourceGenerator s)⁻¹ * kernelProduct m * sourceGenerator s :=
        congrArg (fun x => (sourceGenerator s)⁻¹ * x * sourceGenerator s) hw
      _ = kernelProduct n := source_action_step ha s m n he

/-- The finite certificate needs only the original-word arithmetic law. -/
theorem single_orbit_witness_of_source_action (ha : SourceActionLaw) : SingleOrbitWitness := by
  choose w hw using fun i : Fin 1386 => reachable_realize ha (finiteCertificate.reachable i)
  refine ⟨w, ?_⟩
  intro i j hij
  apply finiteCertificate.injective
  exact @kernelProduct_injective (finiteCertificate.value i) (finiteCertificate.value j)
    ((hw i).symm.trans (hij.trans (hw j)))

/-- 1386 distinct actual conjugates of the original max2 plane word. -/
theorem single_orbit_witness : SingleOrbitWitness :=
  single_orbit_witness_of_source_action source_action_law

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer

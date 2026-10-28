module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.MixedCovariance

/-!
# Constructed triality positive relations on the literal source quotient

The compatible middle-root tensor basis gives the lifted trace pairings
and short--short product. Its diagonal action gives all positive
short-coroot characters. Together with the already constructed long-coroot
action these characters prove covariance of the actual highest mixed
coefficient. The existing polarization argument then forces g(a,b)=N(a)b²,
including the binary fixed field.

All earlier module equations are thus discharged on one aligned source
pinning. Construct the literal PositiveRootData and apply both the original
and geometric range consumers with their unchanged quotient maps. Negative
roots and signed Weyl actions use this same pinning. The remaining signed
torus laws and full Borel/endpoint comparison are subsequent obligations;
this module does not assert the full source recognition theorem.

Every positive binary exponent (including q=2 and q=4), either orientation,
and the original cubic field with its actual fixed-field inclusion are
retained. The earlier geometric and structural row hypotheses remain the
inputs of the independent source assembly owner.

Source: Fong--Seitz I (6E)(b), printed p.43; II (9.27)--(9.35), printed
pp.219--220, with the compatible module comparison on pp.218--219.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Representation Representation.SL2.BinarySmall
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorPositiveApplication
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))
  {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "i" => indices 0
local notation "j" => indices 1
local notation "si" => UnitarySource.actorReflection Q split i
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "w" => GeometricScalars.alignedPlacement Q split σ indices hVi hVj μi μj hm row e
local notation "hs" => GeometricScalars.aligned_short_range Q split σ indices hVi hVj μi μj hm row e
local notation "hl" => GeometricScalars.aligned_long_range Q split σ indices hVi hVj μi μj hm row e
local notation "cc" => StructuralApplication.positiveCommutations Q split (q) (w) (hs) (hl) hm row


local notation "mixedG" => TensorModuleApplication.mixedCoefficient Q split σ indices hVi hVj μi μj hm row e

/-- The missing covariance is now proved for the coefficient chosen from
the actual source mixed product. -/
theorem covariance : CoefficientCovariance e (mixedG) := by
  obtain ⟨hAs,hAl⟩ := TensorTorus.constructed_weights Q split σ indices hVi hVj μi μj hm row e
  have hf : Function.Injective ((q).l 2) := by
    intro a b h
    exact Multiplicative.ofAdd.injective
      ((q).longOrbit_injective
        (GeometricLongRoots.aligned_long_injective Q split σ indices hVi hVj μi μj hm row e) 2 h)
  apply coefficient_covariance_of_weights (q) e (mixedG)
    (TensorModuleApplication.mixed_product Q split σ indices hVi hVj μi μj hm row e)
    hf hAs hAl
  · intro t r a
    fin_cases r
    · have hh := GeometricScalars.hB_short Q split σ indices hVi hVj μi μj hm row e t a
      rw [RankOnePair.hB_parameter] at hh
      change (q).longMap (tor t)*(q).s 0 a*((q).longMap (tor t))⁻¹ = (q).s 0 (t.val.val⁻¹*a)
      simpa only [mul_comm] using hh
    · have hh := GeometricScalars.hB_signed_short Q split σ indices hVi hVj μi μj hm row e t true 1 a
      rw [RankOnePair.hB_parameter,RankOnePair.signedRoots_short,RankOnePair.signedRoots_short,
        RankOnePair.markedShort_one,RankOnePair.markedShort_one] at hh
      exact hh
    · change (q).longMap (tor t)*(q).s 2 a*((q).longMap (tor t))⁻¹ = (q).s 2 (1*a)
      rw [one_mul]
      exact ((q).longMap_commute_short2 (cc) (tor t) a).mul_inv_cancel
  · intro t r a
    have hh := GeometricLongRoots.hB_signed_long Q split σ indices hVi hVj μi μj hm row e t true r a
    rw [RankOnePair.hB_parameter,RankOnePair.signedRoots_long,RankOnePair.signedRoots_long] at hh
    exact hh

/-- The original highest mixed coefficient is the cubic norm times the
square of the fixed-field parameter, uniformly including q=2. -/
theorem mixedCoefficient_eq (a : F) (b : K) : (mixedG) a b = e.norm a*b^2 := by
  obtain ⟨θ,hθ⟩ := scalarMarking_exists_nonfixed e
  let d := TensorModuleApplication.earlierModuleEquations Q split σ indices hVi hVj μi μj hm row e
    (covariance Q split σ indices hVi hVj μi μj hm row e) θ
  exact (ModuleApplication.coefficientStage Q split (q) (w) (hl) e hm
    (StructuralApplication.moduleStage Q split (q) (w) (hs) (hl) hm row
      (GeometricLongRoots.aligned_long_injective Q split σ indices hVi hVj μi μj hm row e)
      e θ hθ d)).toCoefficientStage.coefficient a b

/-- The complete normalized source mixed commutator, as a literal group
equality with all four factors and the original root labels. -/
theorem mixed_product (a : F) (b : K) :
    rightCommutator ((q).l 0 b) ((q).s 0 a) =
      (q).s 1 (a*b.val)*(q).s 2 (σ a*σ (σ a)*b.val)*
        (q).l 1 (e.norm a*b)*(q).l 2 (e.norm a*b^2) := by
  rw [TensorModuleApplication.mixed_product,mixedCoefficient_eq]

/-- Positive-root data in the literal source quotient, with every module
and coefficient equation discharged, including q=2. -/
def positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  TensorModuleApplication.positiveData Q split σ indices hVi hVj μi μj hm row e
    (covariance Q split σ indices hVi hVj μi μj hm row e)
    (Classical.choose (scalarMarking_exists_nonfixed e))
    (Classical.choose_spec (scalarMarking_exists_nonfixed e))

/-- Negative roots and the signed Weyl actions come from the same
constructed pinning as the now proved positive data. -/
def signedData : TrialityPresentation.SignedRootData
    (positiveData Q split σ indices hVi hVj μi μj hm row e) where
  negativeShort r := (q).dihedral.W.toMonoidHom.comp ((q).markedShort r)
  negativeLong r := (q).dihedral.W.toMonoidHom.comp ((q).longOrbit r)
  actions := (q).actions e

@[simp] theorem signedData_roots :
    (signedData Q split σ indices hVi hVj μi μj hm row e).roots = (q).signedRoots e := rfl

/-- The geometric marking retains its actual S image under the same Q.q. -/
theorem nativeHom_range_marked
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split σ indices hVi hVj μi μj hm row e).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split σ indices hVi hVj μi μj hm row e).nativeHom_range_marked marking h

/-- The original numerator retains the literal quotient image of S. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hVi₀ : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj₀ : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (μi₀ : localGroup Q₀ split₀ i ≃* PSL(2,F))
    (μj₀ : localGroup Q₀ split₀ j ≃* PSL(2,K))
    (hm₀ : rotationOrder Q₀ = 6) (row₀ : StructuralRow Q₀ split₀ i j) :
    (positiveData Q₀ split₀ σ indices hVi₀ hVj₀ μi₀ μj₀ hm₀ row₀ e).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorPositiveApplication

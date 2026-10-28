module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorShortProducts

/-!
# Applying the constructed source tensor equations

The compatible tensor basis supplies the literal trace pairings, the full
short--short product and all but the last coefficient of the mixed product
in the actual source quotient. Choose that last coefficient from the proved
group equality. These results discharge the earlier module equations,
retaining only covariance of this constructed coefficient as an explicit
obligation of the source reconstruction. No tensor comparison, basis
pairing or product formula is assumed.

The resulting conditional positive-root data feeds both the original and
geometric marked consumers, preserving their literal quotient maps and S
images, for either orientation and all positive binary exponents. This is
not yet the full signed source comparison. TensorPositiveApplication
discharges covariance and normalization; the remaining signed torus laws
and full marked comparison stay with this source reconstruction owner.

Source: Fong--Seitz II (9.27)--(9.35), printed pp.219--220.
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
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorModuleApplication
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


/-- The remaining coefficient is chosen from an actual mixed product in
this source group, with all other factors already determined. -/
def mixedCoefficient (a : F) (t : K) : K :=
  Classical.choose ((TensorMiddleRoots.constructed_relations Q split σ indices hVi hVj μi μj hm row e).2.2 a t)
local notation "mixedG" => mixedCoefficient Q split σ indices hVi hVj μi μj hm row e

/-- The complete mixed equality in the source group, before the last
coefficient's torus covariance and normalization. -/
theorem mixed_product (a : F) (t : K) :
    rightCommutator ((q).l 0 t) ((q).s 0 a) =
      (q).s 1 (a*t.val) * (q).s 2 (σ a*σ (σ a)*t.val) *
        (q).l 1 (e.norm a*t) * (q).l 2 ((mixedG) a t) :=
  Classical.choose_spec ((TensorMiddleRoots.constructed_relations Q split σ indices hVi hVj μi μj hm row e).2.2 a t)

/-- The three literal basis equations (9.27) follow from the full source
trace pairing; no coordinate or basis pairing assumption remains. -/
theorem basis_pairing (θ : F) (a : F) (b : K) (r : Fin 3) :
    rightCommutator ((q).s 2 (b.val*θ^r.val)) ((q).s 0 a) =
      (q).l 1 (e.trace (a*(b.val*θ^r.val))) :=
  (TensorMiddleRoots.constructed_relations Q split σ indices hVi hVj μi μj hm row e).1 a _


/-- Discharge all earlier module equations except the explicitly retained
covariance of the constructed highest mixed coefficient. -/
def earlierModuleEquations (hcov : CoefficientCovariance e (mixedG)) (θ : F) : EarlierModuleEquations (q) e θ where
  f a b := e.trace (a*σ b*σ (σ b))
  g := mixedG
  τ := RingEquiv.refl K
  basis_pairing := basis_pairing Q split σ indices hVi hVj μi μj hm row e θ
  short_short := TensorShortProducts.constructed_short_product Q split σ indices hVi hVj μi μj hm row e
  mixed := mixed_product Q split σ indices hVi hVj μi μj hm row e
  long_twisted a b := by
    simpa only [RingEquiv.refl_apply,mul_comm] using
      GeometricLongRoots.long_long Q split σ indices hVi hVj μi μj hm row e a b
  covariance := hcov

/-- Feed the constructed source equations to the literal positive-root
consumer. Covariance remains a source obligation of this same theorem family. -/
def positiveData (hcov : CoefficientCovariance e (mixedG)) (θ : F) (hθ : σ θ ≠ θ) :
    TrialityPresentation.PositiveRootData Q split n hn σ :=
  StructuralApplication.positiveData Q split (q) (w) (hs) (hl) hm row
    (GeometricLongRoots.aligned_long_injective Q split σ indices hVi hVj μi μj hm row e)
    e θ hθ (earlierModuleEquations Q split σ indices hVi hVj μi μj hm row e hcov θ)

/-- The geometric marking retains its actual S image under the same Q.q. -/
theorem nativeHom_range_marked (hcov : CoefficientCovariance e (mixedG)) (θ : F) (hθ : σ θ ≠ θ)
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split σ indices hVi hVj μi μj hm row e hcov θ hθ).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split σ indices hVi hVj μi μj hm row e hcov θ hθ).nativeHom_range_marked marking h

/-- The original numerator retains the literal quotient image of S;
there is no descent from a universal completion to an original group. -/
theorem nativeHom_range_original
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hVi₀ : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj₀ : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (μi₀ : localGroup Q₀ split₀ i ≃* PSL(2,F))
    (μj₀ : localGroup Q₀ split₀ j ≃* PSL(2,K))
    (hm₀ : rotationOrder Q₀ = 6) (row₀ : StructuralRow Q₀ split₀ i j)
    (hcov₀ : CoefficientCovariance e
      (mixedCoefficient Q₀ split₀ σ indices hVi₀ hVj₀ μi₀ μj₀ hm₀ row₀ e))
    (θ : F) (hθ : σ θ ≠ θ) :
    (positiveData Q₀ split₀ σ indices hVi₀ hVj₀ μi₀ μj₀ hm₀ row₀ e hcov₀ θ hθ).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorModuleApplication

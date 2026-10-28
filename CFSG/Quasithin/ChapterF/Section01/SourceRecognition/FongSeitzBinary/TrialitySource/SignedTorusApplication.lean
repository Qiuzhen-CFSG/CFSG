module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.SignedTorus
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorPositiveApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GeometricWeylTorus

/-!
# Complete signed torus relations on the constructed source pinning

Combine the tensor short-coroot weights with the natural and long-root
weights already proved on the aligned pinning. The short middle-root label
retains its Frobenius shift. The longest word supplies all inverse weights,
and the long three-root Weyl word supplies the central Weyl--torus law.
Together with the existing arms law and the common abelian Cartan, this
constructs every field of the presentation's TorusRelations.

All equations are in the original marked quotient, for either orientation
and every positive binary exponent, including q=2 and q=4. The same source
extension marking and its restricted fixed-field marking are retained.
FullApplication applies these relations to the full marked comparison.

Source: Fong--Seitz I (6E)(b), printed p.43; II §7 and (9.31), printed p.219;
GLS3 2.4.7--8, with the checked presentation's left-conjugation convention.
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
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.SignedTorusApplication
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

local notation "L" => RankOnePair.signedRoots (q) e
local notation "p" => GeometricApplication.pair Q split σ indices hVi hVj μi μj hm row
local notation "η" => GeometricScalars.scalarAutomorphism Q split σ indices hVi hVj μi μj hm row e

/-- Both aligned coroot factors remain in the same abelian full Cartan. -/
theorem torus_factors_commute (a : (ExtensionField (binaryParameters n hn))ˣ)
    (b : (fixedField (binaryParameters n hn))ˣ) : Commute ((L).hA a) ((L).hB b) := by
  let u : Kˣ := Units.map e.fixed.symm.toMonoidHom b
  have hu : Units.map e.fixed.toMonoidHom u = b := by ext; simp [u]
  rw [← hu]
  change Commute (((p).relabelLong (η).symm).signedRoots e |>.hA a)
    ((((p).relabelLong (η).symm).signedRoots e).hB (Units.map e.fixed.toMonoidHom u))
  rw [RankOnePair.relabelLong_hA,RankOnePair.relabelLong_hB]
  exact GeometricApplication.torus_factors_commute Q split σ indices hVi hVj μi μj hm row e a _

/-- Multiplication for the actual aligned two-parameter torus. -/
theorem torus_mul (a b : TorusParameters n hn) :
    (L).torus (a*b) = (L).torus a*(L).torus b :=
  StructuralApplication.signed_torus_mul_of_cross_commuting Q (q) e
    (torus_factors_commute Q split σ indices hVi hVj μi μj hm row e) a b

/-- All three positive short characters, including the middle-root Frobenius shift. -/
theorem positive_short (a : TorusParameters n hn) (r : Fin 3)
    (x : ExtensionField (binaryParameters n hn)) :
    (L).torus a*(L).shortSigned true r x*((L).torus a)⁻¹ =
      (L).shortSigned true r ((shortCharacter a r).val*x) := by
  apply (q).positive_short_of_weights e
    (TensorTorus.constructed_weights Q split σ indices hVi hVj μi μj hm row e).1
  intro u r z
  exact GeometricScalars.hB_signed_short Q split σ indices hVi hVj μi μj hm row e u true r z

/-- All three positive long characters in the actual fixed field. -/
theorem positive_long (a : TorusParameters n hn) (r : Fin 3)
    (x : fixedField (binaryParameters n hn)) :
    (L).torus a*(L).longSigned true r x*((L).torus a)⁻¹ =
      (L).longSigned true r ((longCharacter a r).val*x) := by
  apply (q).positive_long_of_weights e
    (TensorTorus.constructed_weights Q split σ indices hVi hVj μi μj hm row e).2
  intro u r z
  exact GeometricLongRoots.hB_signed_long Q split σ indices hVi hVj μi μj hm row e u true r z

/-- The complete torus contract is now proved on the same source pinning. -/
theorem torusRelations : (L).TorusRelations where
  mul := torus_mul Q split σ indices hVi hVj μi μj hm row e
  short := (q).signed_short_of_positive e
    (positive_short Q split σ indices hVi hVj μi μj hm row e)
  long := (q).signed_long_of_positive e
    (positive_long Q split σ indices hVi hVj μi μj hm row e)
  arms := GeometricWeylTorus.arms Q split σ indices hVi hVj μi μj hm row e
  central := (q).central_of_long_weights e
    (torus_mul Q split σ indices hVi hVj μi μj hm row e)
    (positive_long Q split σ indices hVi hVj μi μj hm row e)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.SignedTorusApplication

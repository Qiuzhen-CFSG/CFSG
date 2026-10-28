module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.NaturalScalarAction

/-!
# The natural source module on constructed geometric pinnings

Both rank-one pinnings and both coroot placements come from the same
literal quotient geometry. Their full Cartan is abelian. Applying the
constructed radical-section action therefore produces its actual fixed-field
scalar automorphism, with no separately supplied linear action or coefficient.
Relabel the entire long actor by its inverse. The leading mixed commutator
in U/(E D F) and the mixed short-root torus weight then have the required
included-field parameters. The original Weyl lifts, both signs, and all
long-root coordinates use that same relabeling.

This is the natural half of the comparison on Fong--Seitz II pp.218--219.
The eight-dimensional twisted-tensor action, its lifted coefficients and
covariance remain obligations; the final full marked comparison is not
asserted here. Both orientations and every positive binary exponent are
retained, including q=2 and q=4. The quotient is always the original Q.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricScalars
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "p" => GeometricApplication.pair Q split σ indices hVi hVj μi μj hm row
local notation "w" => GeometricApplication.placement Q split σ indices hVi hVj μi μj hm row
local notation "hs" => GeometricApplication.short_range Q split σ indices hVi hVj μi μj hm row
local notation "hl" => GeometricApplication.long_range Q split σ indices hVi hVj μi μj hm row
local notation "hf" => GeometricPinning.short_injective Q split σ indices hVi hVj μi μj
  (UnitarySource.actorReflection Q split (indices 0))
  (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal
local notation "hTs" => GeometricPinning.short_cartan Q split σ indices hVi hVj μi μj
  (UnitarySource.actorReflection Q split (indices 0))
  (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal
local notation "hTl" => GeometricPinning.long_cartan Q split σ indices hVi hVj μi μj
  (UnitarySource.actorReflection Q split (indices 0))
  (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal
variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

/-- The field automorphism read from the geometrically constructed natural action. -/
def scalarAutomorphism : K ≃+* K :=
  NaturalScalarAction.scalarAutomorphism Q split p w hs hl hm hVi hVj row hf hTs hTl e

local notation "η" => scalarAutomorphism Q split σ indices hVi hVj μi μj hm row e

/-- One relabeling of the entire constructed long pinning. -/
def alignedPair : RankOnePair σ (X ⧸ Q.D) := (p).relabelLong (η).symm

local notation "q" => alignedPair Q split σ indices hVi hVj μi μj hm row e

/-- The original chosen Weyl lifts remain the same literal source lifts. -/
def alignedPlacement : WeylPlacement Q q := (w).relabelLong Q p (η).symm

theorem aligned_short_range : ((q).shortOrbit 0).range = simpleRoot Q split (indices 0) :=
  ((p).relabelLong_short_range (η).symm 0).trans hs

theorem aligned_long_range : ((q).longOrbit 0).range = simpleRoot Q split (indices 1) :=
  ((p).relabelLong_long_range (η).symm 0).trans hl

/-- The normalized mixed Cartan character uses the actual source fixed-field inclusion. -/
theorem hB_short (t : Kˣ) (a : F) :
    ((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*(q).s 0 a*
      (((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
        (q).s 0 (a*t.val.val⁻¹) :=
  NaturalScalarAction.relabeled_hB_short Q split p w hs hl hm hVi hVj row hf hTs hTl e t a

/-- Every signed short-root weight of the long coroot, in the presentation's
own scalar marking and its Frobenius-shifted third short root. -/
theorem hB_signed_short (t : Kˣ) (positive : Bool) (i : Fin 3) (a : F) :
    ((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*
      ((q).signedRoots e).shortSigned positive i (e.extension a)*
      (((q).signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    ((q).signedRoots e).shortSigned positive i
      (e.extension ((if positive then ![t.val.val⁻¹,t.val.val,1] i
        else (![t.val.val⁻¹,t.val.val,1] i)⁻¹)*a)) :=
  NaturalScalarAction.relabeled_hB_signed_short Q split p w hs hl hm hVi hVj row hf hTs hTl e
    t positive i a

/-- The source section now has the ordinary leading coefficient for all q.
Normality is only in the literal U; it is constructed internally. -/
theorem leading_commutator :
    let : ((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U).Normal :=
      NaturalSectionApplication.positive_normal Q split p w hs hm hVi row
    ∀ (a : F) (b : K),
      rightCommutator
        (ScalarAlignment.sectionA Q split p w hs
          ((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U) (.ofAdd a))
        (ScalarAlignment.sectionB Q split q (alignedPlacement Q split σ indices hVi hVj μi μj hm row e)
          (aligned_long_range Q split σ indices hVi hVj μi μj hm row e)
          ((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U) (.ofAdd b)) =
      ScalarAlignment.sectionC Q split p w hs hl hm
        ((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U) (.ofAdd (a*b.val)) := by
  let : ((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U).Normal :=
    NaturalSectionApplication.positive_normal Q split p w hs hm hVi row
  exact NaturalScalarAction.normalized_commutator Q split p w hs hl hm hVi hVj row hf hTs hTl e
    (hN := inferInstanceAs
      (((middleRoots Q split (indices 0) (indices 1)).subgroupOf split.U).Normal))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricScalars

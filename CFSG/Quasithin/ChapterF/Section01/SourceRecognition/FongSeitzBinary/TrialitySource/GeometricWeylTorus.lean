module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylTorus
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GeometricScalars

/-!
# The short Weyl--torus equation on the aligned source pinning

The constructed natural action already gives both signed simple short-root
weights of the long coroot. Apply the Weyl-word calculation to those proved
weights to obtain the cross-Weyl equation and the full arms clause of the
checked signed presentation. All parameters, Weyl lifts and torus words
belong to the same geometrically constructed and whole-actor-aligned
pinning of the original quotient. The fixed field is included through the
restriction of the same extension marking, in both source orientations.

No additional weight or Weyl--torus relation is assumed here. The tensor
module equations, remaining short-coroot weights and central Weyl clause
still have to be constructed before full marked recognition. Every positive
binary exponent, including q=2 and q=4, is retained.

Source: Fong--Seitz II §7 and (9.31), printed p.219; GLS3 2.4.7--8.
-/

@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Triality.Standard.ConcreteBruhat.TorusCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricWeylTorus
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
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "L" => RankOnePair.signedRoots (q) e


/-- Conjugation of the original long coroot follows from the proved natural weights. -/
theorem short_weyl_long_torus (u : Kˣ) :
    (q).dihedral.A ((q).longMap (tor u)) =
      (q).shortMap (tor (Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u))*
        (q).longMap (tor u) := by
  apply (q).short_weyl_long_torus_of_weights e u
  intro positive a
  simpa only [Matrix.cons_val_zero,inv_inv] using
    GeometricScalars.hB_signed_short Q split σ indices hVi hVj μi μj hm row e u positive 0 a

/-- The exact short-Weyl torus equation on the aligned source pinning. -/
theorem arms (a : TorusParameters n hn) :
    (L).nA 1*(L).torus a*((L).nA 1)⁻¹ =
      (L).torus (fixedUnit (binaryParameters n hn) a.2/a.1,a.2) := by
  apply (q).arms_of_weights e _ a
  intro u positive x
  simpa only [Matrix.cons_val_zero,inv_inv] using
    GeometricScalars.hB_signed_short Q split σ indices hVi hVj μi μj hm row e u positive 0 x
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.GeometricWeylTorus

module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Definitions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.IntrinsicCenter.Pairing

/-!
# The finite arithmetic contract for the original max2 pair

An increasing product has a central correction for each repeated noncentral
factor and each out-of-order pair of factors. The exact commutator table is
already certified on the literal local words. These definitions retain that
central bit; passing just to the twelve-dimensional central quotient loses
three quarters of the required pair witnesses.

`SourceActionLaw` is the still separate soundness assertion for this arithmetic
in the original source subgroup. `OrbitCertificate` asks only for a tree of
5544 distinct pairs, with no exhaustiveness requirement.

Source: the retained ATLAS J4G1-max2W1 words and
NormalClosureControl/Certificates/source/kernel_candidate.json;
Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open NormalClosureControl NormalClosureControl.IntrinsicCenter LowerBound

/-- Central correction when two increasing-bit words are multiplied. -/
def correction (a b : ℕ) : Bool :=
  (List.ofFn (fun i : Fin 13 =>
    a.testBit i.val &&
      ((decide (i.val ≠ 0) && b.testBit i.val) ^^
        (List.ofFn (fun j : Fin 13 =>
          decide (j < i) && b.testBit j.val && commutatorForm i j)).foldr Bool.xor false)
    )).foldr Bool.xor false

/-- Full thirteen-bit product, including the central sign. -/
def maskMultiply (a b : ℕ) : ℕ :=
  (a ^^^ b) ^^^ (correction a b).toNat

/-- Right conjugation, with false selecting the original X and true selecting Y. -/
def maskAction (useY : Bool) (m : ℕ) : ℕ :=
  (List.finRange 13).foldl (fun r i =>
    if m.testBit i.val then
      maskMultiply r (if useY then Certificates.yMasks i else Certificates.xMasks i)
    else r) 0

/-- The actual original max2 generator used at a tree edge. -/
def sourceGenerator (useY : Bool) : sourceSubgroup :=
  if useY then sourceY else sourceX

/-- Soundness must concern the literal increasing-bit products, not a group label. -/
def SourceActionLaw : Prop :=
  ∀ (useY : Bool) (m : Fin 8192),
    (sourceGenerator useY)⁻¹ * kernelProduct m * sourceGenerator useY =
      maskProduct kernelFactor (maskAction useY m.val)

/-- A finite rooted tree of distinct mask pairs, with actual right-action edges. -/
structure OrbitCertificate where
  masks : Fin 5544 → Fin 8192 × Fin 8192
  parent : Fin 5544 → Fin 5544
  useY : Fin 5544 → Bool
  root : masks 0 = (6607, 3400)
  decrease : ∀ i, i ≠ 0 → (parent i).val < i.val
  edge : ∀ i, i ≠ 0 →
    (maskAction (useY i) (masks (parent i)).1.val,
      maskAction (useY i) (masks (parent i)).2.val) =
    ((masks i).1.val, (masks i).2.val)
  injective : Function.Injective masks

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData

module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeData
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Certificate

/-!
Checked ranks of literal row-eight displacement products. The witnesses use
the original ATLAS basis; their arithmetic is verified by the Lean kernel.
Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988),
pp.484–510. Original matrix attribution is retained in Janko4.Model.Data.
-/

@[expose] public section
open Janko4 Janko4.GeneratorCertificates
open Janko4.LocalStructure.SylowNormalEights
open Janko4.LocalStructure.SylowNormalEights.MatrixRealization
open Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeEight
attribute [local irreducible] modelGroup matrixA matrixB

theorem rows_displacement (a b : ℕ → ℕ)
    (h : ∀ i : Fin 112, a i.val ^^^ 2^i.val = b i.val) :
    rowsMatrix a - 1 = rowsMatrix b := by
  rw [← decode_ofFn a, ← decode_ofFn b, ← decode_displacement]
  apply congrArg decodeRows
  apply Vector.ext
  intro i hi
  change (displacement (Vector.ofFn (fun j : Fin 112 => a j.val))).get ⟨i, hi⟩ =
    (Vector.ofFn (fun j : Fin 112 => b j.val)).get ⟨i, hi⟩
  simpa only [displacement, get_ofFn] using h ⟨i, hi⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeEight

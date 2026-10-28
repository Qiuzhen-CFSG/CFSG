module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.Coordinates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PC15Rank
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers
import Mathlib.Tactic.FinCases

/-!
# Literal Mathieu kernel and nine invariant rank-span certificates

The eleven published ascending words evaluate to the original eleven Mathieu
kernel basis elements. Their generated subgroup is therefore the embedded
literal kernel, by the existing basis-generation theorem. This comparison
uses the marked words and the actual inclusion in J₄.

Complete subgroup coordinates give the nine candidate orders. The checked
displacement fibers supply rows 0–4, and the checked whole-subgroup pair counts
supply rows 5–8. Together they give the exact generated rank-span orders,
with no remaining realization, rank, or coverage premise.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48;
Kleidman–Wilson (1988), pp.484–510. The matrix-realization producer retains
the ATLAS attribution and checked evaluations.
-/

public section

open Janko4 Subgroup Janko4.LocalStructure.SylowNormalEights
open Janko4.OuterReduction.OddIndex
open Janko4.Cardinality Janko4.LocalStructure
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

private def kernelWordAt (i : Fin 11) : List (Fin 21) :=
  kernelWords[i.val]'(by simpa only [kernelWords, List.length_cons, List.length_nil] using i.isLt)

private theorem kernelWordAt_eval (i : Fin 11) :
    ((kernelWordAt i).map (fun j => (MatrixWords.pcGenerator j : Model))).prod =
      twoGenerator (.inl i) := by
  have h : MatrixWords.literalGenerator (.inl i) =
      ((kernelWordAt i).map MatrixWords.pcGenerator).prod := by
    fin_cases i
    · exact MatrixRealization.literal0_word
    · exact MatrixRealization.literal1_word
    · exact MatrixRealization.literal2_word
    · exact MatrixRealization.literal3_word
    · exact MatrixRealization.literal4_word
    · exact MatrixRealization.literal5_word
    · exact MatrixRealization.literal6_word
    · exact MatrixRealization.literal7_word
    · exact MatrixRealization.literal8_word
    · exact MatrixRealization.literal9_word
    · exact MatrixRealization.literal10_word
  have hh := congrArg twoSubgroup.subtype h
  simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
    MatrixWords.literalGenerator] using hh.symm

private theorem kernelWords_eq : kernelWords = List.ofFn kernelWordAt := by decide +kernel

/-- The published PC marking generates exactly the eleven original kernel basis words. -/
theorem matrixKernel_eq_orderSpectrumKernel : matrixKernel = orderSpectrumKernel := by
  have he : Set.range (fun w : {w : List (Fin 21) // w ∈ kernelWords} =>
      (w.val.map (fun j => (MatrixWords.pcGenerator j : Model))).prod) =
      Set.range (fun i : Fin 11 => twoGenerator (.inl i)) := by
    ext x
    constructor
    · rintro ⟨⟨w, hw⟩, rfl⟩
      rw [kernelWords_eq, List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw
      exact ⟨i, (kernelWordAt_eval i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨kernelWordAt i, by rw [kernelWords_eq]; exact List.mem_ofFn.mpr ⟨i, rfl⟩⟩,
        kernelWordAt_eval i⟩
  change Subgroup.closure _ = (localKernel matrixA_mul_self matrixB_pow_four).map _
  rw [he, ← Janko4.Cardinality.QuotientCount.Image.closure_basis_eq_localKernel,
    MonoidHom.map_closure, ← Set.range_comp]
  rfl

/-- Exact orders of all nine literal candidates and their complete invariant fiber spans. -/
theorem rankCertificates : RankCertificates := by
  intro i
  refine ⟨MatrixCertificates.matrixFamily_card i, ?_⟩
  by_cases hi : i.val < 5
  · exact MatrixCertificates.displacement_span_orders i hi
  · exact MatrixCertificates.pairCount_span_orders i (Nat.le_of_not_gt hi)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders

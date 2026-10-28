module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.RankReduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.FourGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PairRanks
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Comparison
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking

/-!
# The two exceptional pure-kernel normalizer obstructions

For candidate 2, the checked marking and plane-centralizer count put its full
ambient normalizer strictly inside an explicit conjugate of proper max4.
The two pointwise comparisons in `ThirdConjugacy` identify the literal plane
with candidate 2, using the original kernel coordinates and left conjugation.
For candidate 5, the certified pair-displacement rank test identifies candidate 2
as a proper nonzero subgroup preserved by the full ambient normalizer.

The final theorem discharges every centralizer, marking, conjugacy and rank
premise. It supplies the two obstructions consumed by
`exceptional_candidate_not_fixed` and
`smallKernelClosureOrders_of_pure_certificates`; exhaustion of the kernel
candidates remains a separate input of that parent assembly.

Source context: Aschbacher--Smith A.3.12, printed pp.47--48;
Kleidman--Wilson (1988), pp.484--510. The coordinate and matrix provenance is
retained in the imported literal max1 and max4 modules.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear PureNormalizers
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

namespace PureNormalizers

/-- The actual pointwise matrix comparisons identify the embedded plane.
These are the images of max4-eight indices 1 and 2 in `ThirdConjugacy`. -/
theorem max4Plane_map_eq_candidate_two (k : Model)
    (h1 : (MulAut.conj k) (NormalEight.element 1 : Model) = maskElement 1453)
    (h2 : (MulAut.conj k) (NormalEight.element 2 : Model) = maskElement 1387) :
    max4Plane.map (MulAut.conj k).toMonoidHom = candidate 2 := by
  have h5 : (MulAut.conj k) (NormalEight.element 5 : Model) = maskElement 198 := by
    have he : (NormalEight.element 5 : Model) =
        (NormalEight.element 1 : Model) * (NormalEight.element 2 : Model) :=
      congrArg (fun z : max4Subgroup => (z : Model)) (NormalEight.element_mul 1 2).symm
    rw [he, map_mul, h1, h2, ← maskElement_xor]
    rfl
  apply le_antisymm
  · rintro _ ⟨u, ⟨v, ⟨i, rfl⟩, rfl⟩, rfl⟩
    change (MulAut.conj k) (NormalEight.element (planeIndex i) : Model) ∈ candidate 2
    rw [candidate_two_eq_fourRange]
    fin_cases i
    · change (MulAut.conj k) (NormalEight.element 0 : Model) ∈ fourRange
      rw [NormalEight.element_zero, Subgroup.coe_one, map_one]
      exact fourRange.one_mem
    · change (MulAut.conj k) (NormalEight.element 1 : Model) ∈ fourRange
      rw [h1]
      exact ⟨3, rfl⟩
    · change (MulAut.conj k) (NormalEight.element 2 : Model) ∈ fourRange
      rw [h2]
      exact ⟨1, rfl⟩
    · change (MulAut.conj k) (NormalEight.element 5 : Model) ∈ fourRange
      rw [h5]
      exact ⟨2, rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m = 1387 ∨ m = 198 := by simpa [candidateRows] using hm
    rcases hm' with rfl | rfl
    · rw [← h2]
      exact mem_map_of_mem _ (mem_map_of_mem _
        (show NormalEight.element 2 ∈ localPlane from ⟨2, rfl⟩))
    · rw [← h5]
      exact mem_map_of_mem _ (mem_map_of_mem _
        (show NormalEight.element 5 ∈ localPlane from ⟨3, rfl⟩))

/-- The certified ambient word carries precisely the literal max4 plane to
candidate 2. The target masks use the same embedded kernel coordinates. -/
theorem max4Plane_map_conjugator :
    max4Plane.map (MulAut.conj ThirdConjugacy.conjugator).toMonoidHom = candidate 2 := by
  apply max4Plane_map_eq_candidate_two
  · exact ThirdConjugacy.conjugator_element 1
  · exact ThirdConjugacy.conjugator_element 2

/-- The FULL normalizer of candidate 2 has a strict proper overgroup, namely
the conjugate of literal max4 supplied by the plane comparison. -/
theorem candidate_two_obstruction :
    ∃ H : Subgroup Model,
      normalizer (candidate (exceptionalIndex 0) : Set Model) < H ∧ H < ⊤ :=
  candidate_two_obstruction_of_max4Plane
    (max4Plane_centralizer_le_of_marking Max4EightCentralizer.marking)
    ⟨ThirdConjugacy.conjugator, max4Plane_map_conjugator⟩

end PureNormalizers

/-- Assembly with exactly the full-plane centralizer, literal comparison and
finite pair-rank obligations still explicit. This is not the unconditional theorem. -/
theorem exceptionalNormalizerObstructions_of_plane_and_pair_ranks
    (hC : centralizer (max4Plane : Set Model) ≤ max4Subgroup)
    (hconj : ∃ k : Model, max4Plane.map (MulAut.conj k).toMonoidHom = candidate 2)
    (hrank : SmallPairRanks) : ExceptionalNormalizerObstructions := by
  intro j
  fin_cases j
  · exact Or.inl (candidate_two_obstruction_of_max4Plane hC hconj)
  · exact Or.inr (candidate_five_obstruction_of_pair_ranks hrank)

/-- Unconditional witnesses for both exceptional full ambient normalizers.
Candidate 2 has a strict proper overgroup; candidate 5 preserves candidate 2
as a proper nonzero subgroup. -/
theorem exceptionalNormalizerObstructions : ExceptionalNormalizerObstructions := by
  intro j
  fin_cases j
  · exact Or.inl candidate_two_obstruction
  · exact Or.inr candidate_five_obstruction

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders

module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.StemReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.PeriodArithmetic

/-!
# Ordering the principal eleven-block real stem

`RealStem.row_sign` derives the alternating signs from ordinary orthogonality.
`RealStem.admissible` connects any actual real stem to the exhaustive integer
path certificate. Primitive-root evaluation identifies each negative witness
with a scaled tensor coefficient, contradicting `RealStem.TensorPositive`.
Thus `RealStem.ordered_degree` determines all eleven ordinary vertex degrees.
Construction of the stem and proof of tensor positivity remain separate inputs.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary J1 table and the
cyclic-block real stem; see `../Source.md` and `Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

open PathOrdering

/-- Tensor positivity excludes the negative alternative in the finite path
certificate, so every genuine real stem has the prescribed ordinary degrees. -/
public theorem RealStem.ordered_degree
    {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}
    (s : RealStem G d) (hpos : s.TensorPositive) :
    (fun i => ordinaryDegree (s.row i)) = orderedVertexDegree := by
  rcases s.ordered_or_negative with horder | ⟨i, j, k, n, hn, hneg⟩
  · exact horder
  · exfalso
    have h := congrArg (evaluate d.rootFive d.rootNineteen) hneg
    rw [s.evaluate_tensorNumerator, evaluate_scalar] at h
    apply s.scaled_tableTensor_ne_negative hpos i j k 175560 n hn
    simpa only [s.tensorCoefficient_eq_tableTensor, Nat.cast_ofNat, Int.cast_neg,
      Int.cast_natCast] using h

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

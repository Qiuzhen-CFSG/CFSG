module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Row3
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Row4
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Row8
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Row9
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Row10
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.StemReduction

/-!
# Exhaustive integer elimination of principal eleven-block paths

Every admissible path has ordinary degrees
`1,120,133,120,133,76,56,76,133,120,56`, or an explicit negative scalar
`tensorNumerator`. The search coverage and arithmetic bridges are proved in
`FiniteCertificate.Engine`; the five row modules check every branch using
bounded kernel computations. Equal-degree row orderings remain unrestricted.

The application to `RealStem` uses its proved admissibility. Excluding the
negative alternative additionally needs the separate primitive-root
soundness and tensor-positivity results, which are not assumptions of this
purely integer certificate.

Source: Janko, J. Algebra 3 (1966), 147–186, and the real-stem calculation
of Feit, Chapter VII; see `../Source.md` and `FiniteCertificate/source/README.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

open FiniteCertificate

/-- Every admissible integer path has the prescribed ordinary degrees or
an explicit negative, scalar tensor numerator. Equal-degree rows are not fixed. -/
public theorem ordered_or_negative (r : Fin 11 → Fin 15) (hr : Admissible r) :
    (fun v => ordinaryDegree (r v)) = orderedVertexDegree ∨
      ∃ i j k : Fin 10, ∃ n : ℕ, 0 < n ∧
        tensorNumerator r i j k = scalar (-(n : ℤ)) := by
  have he : 0 < (ordinaryDegree (r 2) : ℤ) - ((ordinaryDegree (r 1) : ℤ) - 1) := by
    simpa [edgeTerms, hr.first, ordinaryDegree] using hr.positive 2
  obtain ⟨ha, hb⟩ := initial_choices (r 1) (r 2) (hr.alternating 1) (hr.alternating 2) he
  have hall : ∀ p ∈ branch (r 1) (r 2), Good (rowOf ([0,r 1,r 2] ++ p)) := by
    rcases ha with ha | ha | ha | ha | ha
    · rw [ha]; exact row3_good (r 2) hb
    · rw [ha]; exact row4_good (r 2) hb
    · rw [ha]; exact row8_good (r 2) hb
    · rw [ha]; exact row9_good (r 2) hb
    · rw [ha]; exact row10_good (r 2) hb
  have h := hall _ (mem_branch hr)
  change Good (rowOf (0 :: tailRows r)) at h
  rw [rowOf_actual hr] at h
  exact h

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

/-- Apply the finite certificate to the literal rows of an actual real stem.
The hypotheses come from ordinary orthogonality and its integer dimensions
through `RealStem.admissible`. -/
public theorem RealStem.ordered_or_negative {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d) :
    (fun v => ordinaryDegree (s.row v)) = orderedVertexDegree ∨
      ∃ i j k : Fin 10, ∃ n : ℕ, 0 < n ∧
        PathOrdering.tensorNumerator s.row i j k = PathOrdering.scalar (-(n : ℤ)) :=
  PathOrdering.ordered_or_negative s.row s.admissible

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

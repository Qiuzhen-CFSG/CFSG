module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalModule
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalLevi
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalFactorization
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.Vectors
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingCentralVector

public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# The ordinary A₇ block exclusion in original 4.3.7

The source configuration supplies compatible coordinates on all of U(K),
the transposition image of R, the five-letter image of L, and the equality
[U(K),L]=[Ω₁Z(O₂(LT)),L]. The Sylow and Levi calculations complete the local
geometry. The explicit vector construction then gives e₁₂, its e₃₄ conjugate
and K=⟨L,Lᵏ⟩. Applying the proved C.6.4 central-vector theorem forces
T≤N_G(K)=H, contradicting the original strict Sylow intersection.

The final source-facing theorem retains the original rank-one hypotheses.
Its only case premise is the A₇ row, supplied by the block-alternatives
assembly owner; every marking and centrality premise is discharged here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
original 4.3.7, printed p.616, using C.6.4(10), pp.167–169.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The whole local geometry, with all coordinate, factorization and Levi
premises discharged on the original source configuration. -/
theorem SourceConfiguration.source_alternating_local_geometry
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    Nonempty (BlockAlternatingLocalGeometry c) := by
  obtain ⟨d⟩ := c.source_alternating_coordinates D hpsl hf ha
  exact ⟨{ toBlockAlternatingCoordinates := d
           factorization := d.sylow_factorization D hpsl
           levi_normalizes := d.levi_normalizes }⟩

/-- The source A₇ configuration supplies the actual e₁₂ vector, its e₃₄
conjugate in the full W, and the ambient generation K=⟨L,Lᵏ⟩. -/
theorem SourceConfiguration.source_alternating_marking
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    Nonempty (BlockAlternatingMarking c) := by
  obtain ⟨d⟩ := c.source_alternating_local_geometry D hpsl hf ha
  exact c.alternating_marking_of_local_geometry ha d

/-- The ordinary A₇ branch of original 4.3.7, with the actual marking and
specialized C.6.4 central-vector conclusion both proved. -/
theorem SourceConfiguration.false_of_alternating_block_four
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (ha : ChapterC.IsAlternatingBlock c.K 7) : False := by
  obtain ⟨d⟩ := c.source_alternating_marking D hpsl hf ha
  exact c.false_of_alternating_marking_centralVector D h d

/-- Source-facing A₇ branch, retaining the original rank-one hypotheses and
field degree. The block-alternatives owner supplies only the A₇ row. -/
theorem source_block_alternating_false
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (_hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (_hb : ChapterC.IsBlock c.K)
    (hn2 : n = 2) (ha : ChapterC.IsAlternatingBlock c.K 7) : False :=
  c.false_of_alternating_block_four D h.toHypothesis1221 (by simpa [hn2] using hpsl) hf ha
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

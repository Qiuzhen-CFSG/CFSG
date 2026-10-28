module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Paired
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPairedPrime
/-!
# The complete original reflected Cartan source

The genuine degree-one generation theorem excludes the last paired odd
PSL2 row whenever n(H)>1. Every remaining actual source component therefore
supplies an attained generation bound, the marked field exponent and the
same Hall subgroup with its reflected cyclic subgroup. The numerical claim
is n(H)≤f; no equality through the solvable maximal core is used.
Source: Aschbacher–Smith E.2.2 and E.6.27, printed pp.215–216,257.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_intrinsic_escape_knownSimple
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hn : 1 < generationParameter H) :
    ∃ f : ℕ, IsEGenerated f H ∧ generationParameter H ≤ f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  rcases source_intrinsic_escape_or_paired_odd hH T hP hn with ho|hg
  · obtain ⟨K,hK,_,hgen,hN,p,hp,_,h7,hm⟩ := ho
    let : Fact p.Prime := ⟨hp⟩
    have hs : ¬Group.IsSolvable H := by
      intro hs
      let := hs
      exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
    have hb := paired_prime_parameter_le_one ChapterA.Section02.theoremA_knownSimple
      hH T hP hs K hK hgen hN (p := p) (by omega) hm
    exact (Nat.not_le_of_gt hn hb).elim
  · exact hg
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted

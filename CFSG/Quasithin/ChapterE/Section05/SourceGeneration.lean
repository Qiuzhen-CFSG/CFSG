module
public import CFSG.Quasithin.ChapterE.Section05.CoreCenter
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter
/-!
# The complete E.5.2 generation argument

The genuine E.5.1 center-containment theorem discharges the remaining
input of the local residual argument. That argument includes both the
component and minimal odd-member branches. The rank-degenerate case is
handled separately, so no rank or local E-member assumption remains.

Generation at a positive index j suffices. The second theorem applies this
to the attained positive source parameter n(G)≤j, preserving the minimum's
explicit empty-set convention. No general E.1.11 existence is asserted.
Source: Aschbacher–Smith E.5.1–2, printed pp.242–243.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup ChapterB
variable {G : Type*} [Group G] [Finite G]
theorem source_E_5_2_of_isEGenerated
    (P : Sylow 2 G) (i j : ℕ) (hj : 0 < j) (hgen : IsEGenerated j G) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ := by
  by_cases hdeg : twoRank (P : Subgroup G) ≤ i + j
  · exact thompsonCentralizerGenerators_eq_top_of_rank_le P i j hdeg
  · apply thompsonCentralizerGenerators_eq_top_of_center P i j hj (Nat.lt_of_not_ge hdeg) hgen
    intro A K hA hK hc
    exact higherThompsonCenter_le_omegaCenter P A K i j hA hK hc

theorem source_E_5_2_of_positive_parameter
    (P : Sylow 2 G) (i j : ℕ) (hpos : 0 < generationParameter G)
    (hn : generationParameter G ≤ j) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ :=
  source_E_5_2_of_isEGenerated P i j (lt_of_lt_of_le hpos hn)
    ((isEGenerated_generationParameter_of_pos hpos).mono hn)
end CFSG.Quasithin.ChapterE

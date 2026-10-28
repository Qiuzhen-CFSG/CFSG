module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Marking
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.ModelCounts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Overgroup

/-!
# The A₈ overgroup has index one or nine

The centralizer order marks z as a four-transposition involution of L, and
the thirteen-element core fusion separates the two involution classes.
The local intersection family gives odd index. If both full involution
centralizers lie in L, the pair-counting formula forces L = G. Otherwise
the two-residual of the second centralizer is recognized as A₅, and its
extension gives an actual comparison with the corresponding centralizer in A₉.
The checked mixed-pair counts 156 and 555, with centralizer orders 192 and
480, give |G| = 181440 and |G:L| = 9 by Thompson's order formula.

`index_alternative_of_source` discharges the marking, centralizer comparison
and model counts from the original source inputs and the supplied A₈
equivalence. The existing faithful coset-action endpoint then gives the
actual A₈ or A₉ model without an ambient simplicity hypothesis. The parent
I.4.6 assembly retains construction of the local intersection family,
thirteen-element core fusion and A₈ subgroup. Earlier conditional interfaces
are preserved below.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38; Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Conditional assembly of the index calculation, with source marking,
centralizer recognition, and finite model counts still explicit. -/
public theorem index_alternative_of_marked_source_steps (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    {L : Subgroup G} (hCL : Centralizer z ≤ L) (d : Index.InvolutionData z L)
    (centralizers : ¬ d.K ≤ L → Nonempty (Index.SecondCentralizerData d))
    (counts : Index.ModelCounts) : L = ⊤ ∨ L.index = 9 := by
  by_cases hproper : L = ⊤
  · exact Or.inl hproper
  · have hL := Index.odd_index h local_intersections L hCL
    obtain ⟨c⟩ := centralizers (d.second_centralizer_not_le h.involution hL hCL hproper)
    exact Or.inr (Index.index_nine_of_centralizer_comparison h d hL hCL c counts)

/-- Apply the existing faithful coset-action endpoint to the calculated index.
This retains the three intermediate steps as explicit inputs. -/
public theorem alternating_eight_or_nine_of_marked_source_steps (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    {L : Subgroup G} (hCL : Centralizer z ≤ L) (d : Index.InvolutionData z L)
    (centralizers : ¬ d.K ≤ L → Nonempty (Index.SecondCentralizerData d))
    (counts : Index.ModelCounts) :
    Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) :=
  alternating_eight_or_nine L d.equiv hCL
    (index_alternative_of_marked_source_steps h local_intersections hCL d centralizers counts)

/-- The index alternative in Proposition 3.3, with the marked involution
classes, second-centralizer comparison and finite model counts all proved.
The supplied source geometry and A₈ equivalence are the only earlier inputs. -/
public theorem index_alternative_of_source (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13) (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hCL : Centralizer z ≤ L) :
    L = ⊤ ∨ L.index = 9 := by
  obtain ⟨d⟩ := exists_index_involutionData h h13 L e hCL
  exact index_alternative_of_marked_source_steps h local_intersections hCL d
    (Index.secondCentralizerData_of_source h hn local_intersections h13 L hCL d)
    Index.modelCounts

/-- Apply the existing recognition endpoint to the completed index alternative.
No marking, residual, model-count or ambient simplicity premise remains. -/
public theorem alternating_eight_or_nine_of_source (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13) (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hCL : Centralizer z ≤ L) :
    Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) :=
  alternating_eight_or_nine L e hCL
    (index_alternative_of_source h hn local_intersections h13 L e hCL)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SourceReduction
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.Doubled

/-!
# All natural L₃(2) rows in the original centralizer analysis

The one-copy and doubled-copy transports now construct the orbit markings
directly from the literal third row of 13.1.10. Thus this entire row supplies
both OrbitFacts and SieveActions. Applying it to the genuine source
classification leaves only the deleted S₅ and rank-four extension rows.

The earlier Thompson movement retains its source-supplement discharge owner,
qt-d-1317-source. The remaining two rows and final orbit assembly remain with
qt-d-1317-module-orbits; this reduction does not assert their completion.

Source: Aschbacher--Smith 13.1.10(3) and 13.1.12, printed pp.871--874.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The full third classification row discharges both literal consumer interfaces. -/
theorem LinearThreeMarking.centralizer_inputs
    [IsElementaryAbelian 2 (normalizerMoved L)]
    (d : LinearThreeMarking T L) (h : Context T L p) :
    OrbitFacts T L p ∧ SieveActions h := by
  obtain ⟨r,hr,hr2,ha⟩ := d.copies
  have he : r = 1 ∨ r = 2 := by omega
  rcases he with rfl | rfl
  · exact centralizer_inputs_of_one_copy h ha
  · exact centralizer_inputs_of_two_copies h ha

/-- The source rows still requiring assembly after both natural-copy cases. -/
inductive RemainingExceptionalCentralizerMarking (T : Sylow 2 G) (L : Subgroup G) : Type u
  | symmetricFive (d : SymmetricFiveRow T L)
  | rankFour [IsElementaryAbelian 2 (normalizerMoved L)]
      (d : LinearThreeRankFourMarking T L)

/-- Apply the actual source classification and both natural-copy transports;
no module marking or orbit conclusion is assumed. -/
theorem centralizer_inputs_or_exceptional
    (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    (OrbitFacts T L p ∧ SieveActions h) ∨
      Nonempty (RemainingExceptionalCentralizerMarking T L) := by
  rcases centralizer_inputs_or_remaining h hmove with hi | hd
  · exact Or.inl hi
  · obtain ⟨d⟩ := hd
    cases d with
    | symmetricFive d => exact Or.inr ⟨.symmetricFive d⟩
    | doubledNatural _ ha => exact Or.inl (centralizer_inputs_of_two_copies h ha)
    | rankFour d => exact Or.inr ⟨.rankFour d⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Complete
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.MarkedConsumers
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.Natural

/-!
# Remaining source rows after the natural-cover orbit assembly

Apply the genuine four-way classification under its original hypotheses.
The natural A₅ cover and the single natural L₃(2) copy supply both original
centralizer-consumer inputs. The remaining alternatives retain their actual
action markings and, in the doubled case, precisely two natural copies.

This is a reduction of 13.1.12, not its completed source statement. The
deleted-S₅ Sylow action and the two remaining classification-to-orbit
transports stay with qt-d-1317-module-orbits. The earlier Thompson movement
is discharged by qt-d-1317-source and its source-supplement input.

Source: Aschbacher--Smith 13.1.10--12, printed pp.871--874.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The three original rows whose remaining action transport is still needed. -/
inductive RemainingCentralizerMarking (T : Sylow 2 G) (L : Subgroup G) : Type u
  | symmetricFive (d : SymmetricFiveRow T L)
  | doubledNatural [IsElementaryAbelian 2 (normalizerMoved L)]
      (d : LinearThreeMarking T L)
      (copies : IsRepeatedLinearNatural (componentRepresentation (L := L)) BinaryField.two 3 2)
  | rankFour [IsElementaryAbelian 2 (normalizerMoved L)]
      (d : LinearThreeRankFourMarking T L)

/-- A source-level reduction with the completed rows applied to the literal
centralizer consumer. No classification premise is assumed. -/
theorem centralizer_inputs_or_remaining
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (RemainingCentralizerMarking T L) := by
  obtain ⟨d⟩ := fourWayMarking_of_source h.hypothesis h.many h.maximal h.nonquasisimple hmove
  cases d with
  | pslTwoFour d => exact Or.inl (d.centralizer_inputs h)
  | symmetricFive d => exact Or.inr ⟨.symmetricFive d⟩
  | linearThree d =>
    obtain ⟨r,hr,hr2,ha⟩ := d.copies
    have he : r = 1 ∨ r = 2 := by omega
    rcases he with rfl | rfl
    · exact Or.inl (centralizer_inputs_of_one_copy h ha)
    · exact Or.inr ⟨.doubledNatural d ha⟩
  | linearThreeRankFour d => exact Or.inr ⟨.rankFour d⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

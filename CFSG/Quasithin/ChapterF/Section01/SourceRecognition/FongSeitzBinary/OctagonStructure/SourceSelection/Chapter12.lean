module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Chapter12OctagonFactorAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Chapter12OctagonComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineOctagonExclusion

/-!
# Source-selected octagon branches for the actual Chapter 12 preparation

Apply the refined source catalogue to the literal factors ![L,R] supplied
by Preparation and the full KnownSimple/proper-K hypotheses. The original
linear field has degree greater than one, so the constructed (6H) data
has positive Suzuki parameter. The other branches retain the exact
two-linear degree ratio or the unitary degree parity and cubic-root bounds.
The affine exclusion supplies both original kernel containments and their
literal two-core preimages on this same marked quotient.

This is the source-selection stage of 12.2.2, not the final Ree recognition.
The remaining (6F) and (6G) exclusions and Section 10 comparison are not
assumed as callbacks. Both original quotient maps and full Borels remain
in the constructed (6H) data.
Source: Aschbacher--Smith 12.2.2, F.1.1; Fong--Seitz I (1K), (6F)--(6H).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.ReeSource
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
include D h hmany hn hpsl d hTH hm

/-- The actual Chapter 12 preparation supplies the refined original catalogue,
both original regularities, positive Suzuki parameter and the exact surviving
degree restrictions. -/
theorem rankOne_octagon_source_selection :
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∧
    ((∃ m, 0 < m ∧ Nonempty (OriginalReeSixHData Q e split n m)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
        ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n)) := by
  refine ⟨D.rankOne_octagon_regularity h hmany hn hpsl d hTH Q e split hm, ?_⟩
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases original_octagon_source_selection Q e hf split hm
      (Nat.zero_lt_of_lt hn) hpsl with ⟨m,⟨c⟩⟩ | hremaining
  · have he := c.common_field
    exact Or.inl ⟨m,by omega,⟨c⟩⟩
  · exact Or.inr hremaining

include D h hmany hn hpsl d hTH hm e split in
/-- Consume the constructed `(6H)` branch of the octagon source selection.
The two outstanding linear/unitary alternatives remain literal source
disjuncts; no exhaustive octagon row choice is asserted here. -/
theorem rankOne_octagon_comparison_or_linear_or_unitary :
    Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
        ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) := by
  obtain ⟨_, hrows⟩ := D.rankOne_octagon_source_selection h hmany hn hpsl d hTH Q e split hm
  rcases hrows with ⟨m, hmpos, ⟨c⟩⟩ | hrows
  · rcases ReeSection10.concrete_comparison_ofSixHData Q split e c.toReeSixHData with he | he
    · exact Or.inl (.ree m (Or.inl he))
    · exact Or.inl (.ree m (Or.inr he))
  · exact Or.inr hrows

include e split in
/-- If the actual opposite factor is a degree-one unitary quotient, the
original nonbinary linear field has degree two, four or six. -/
theorem rankOne_octagon_small_unitary_degrees
    (hunitary : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 2 ∨
      IsSU (R ⧸ pCore 2 R) 3 2) : n = 2 ∨ n = 4 ∨ n = 6 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_small_unitary_degrees Q e hf split hm 0 1 (by decide)
    (Nat.zero_lt_of_lt hn) hpsl hunitary

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

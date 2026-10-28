module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OctagonFactorAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original Chapter 12 factors in the octagonal branch

The actual Preparation and full KnownSimple hypothesis supply F.1.1 for
![L,R]. The existing linear assertion and a Suzuki or dihedral assertion
for R construct the full source (6H) data, with both original panel maps,
whole Borels and endpoint squares. The common field excludes the dihedral
case here because the selected linear field has degree greater than one.

The exhaustive opposite-factor split retains the outstanding linear and
unitary cases explicitly. It is a source-selection reduction, not the
final Ree comparison. No Section 10 angular equations are assumed.
Source: Aschbacher--Smith 12.2.2 and F.1.1; Fong--Seitz I (6F)--(6H).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.ReeSource
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
variable
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

/-- Actual original factor assertions construct source (6H), its full Borels
and both endpoint squares. The selected field forces positive Suzuki parameter. -/
theorem rankOne_octagon_sixH_of_suzuki_or_dihedral
    (hother : (∃ a, Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup a)) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* DihedralGroup 5)) :
    ∃ m, 0 < m ∧ Nonempty (OriginalReeSixHData Q e split n m) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨m,⟨c⟩⟩ := original_suzuki_or_dihedral_sixH_data Q e hf split hm n
    (Nat.zero_lt_of_lt hn) hpsl hother
  have he := c.common_field
  exact ⟨m,by omega,⟨c⟩⟩

include e split in
/-- The order-ten quotient is excluded only after its faithful Sz(2) completion
and the actual source common field have been constructed. -/
theorem rankOne_octagon_dihedral_excluded
    (hdihedral : Nonempty ((R ⧸ pCore 2 R) ≃* DihedralGroup 5)) : False := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_nonbinary_linear_dihedral_excluded Q e hf split hm n
    (Nat.zero_lt_of_lt hn) hn hpsl hdihedral

/-- Exhaust F.1.1 at the actual Chapter 12 opposite factor, producing (6H) in
every Suzuki/dihedral case while retaining the precise unresolved source rows. -/
theorem rankOne_octagon_sixH_or_linear_or_unitary :
    (∃ m, 0 < m ∧ Nonempty (OriginalReeSixHData Q e split n m)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b)) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases original_octagon_sixH_or_linear_or_unitary Q e hf split hm n
    (Nat.zero_lt_of_lt hn) hpsl with ⟨m,⟨c⟩⟩ | hremaining
  · have he := c.common_field
    exact Or.inl ⟨m,by omega,⟨c⟩⟩
  · exact Or.inr hremaining

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

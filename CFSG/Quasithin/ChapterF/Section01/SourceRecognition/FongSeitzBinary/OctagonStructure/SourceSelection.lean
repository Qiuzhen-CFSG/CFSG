module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OctagonFactorAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairQuadraticDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryBounds

/-!
# Source selection at an original linear octagon endpoint

The full F.1.1 opposite-factor catalogue reduces to the constructed (6H)
data, an odd linear degree paired with its double, or one of the two
unitary quotients with opposite degree parity and the octagon bounds.
All assertions concern the original factors and the same full amalgam
marking; the (6H) data retains both quotient squares and whole Borels.

The unitary root degree is three times its field degree. Thus the bounds
on a linear/unitary pair are n ≤ 6b and 3b ≤ 2n. The binary linear endpoint
has no unitary alternative. The general (6F) and (6G) contradictions and
the later Ree comparison remain separate source obligations.
Source: Fong--Seitz I (1J)--(1K), (6F)--(6H), pp.6--7,45--56; AS F.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open ReeSource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8)
include h hm

/-- Exhaust the original catalogue, with source parameter restrictions on
both outstanding families and constructed original (6H) data in the Ree branch. -/
theorem original_octagon_source_selection {n : ℕ} (hn : 0 < n)
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    (∃ m, Nonempty (OriginalReeSixHData Q e split n m)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 (2^b) ∧
        ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU ((L 1) ⧸ pCore 2 (L 1)) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) ∨
      (∃ b, 0 < b ∧ IsSU ((L 1) ⧸ pCore 2 (L 1)) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) := by
  rcases original_octagon_sixH_or_linear_or_unitary Q e h split hm n hn hlinear with
    hree | ⟨b,hb,hblinear⟩ | ⟨b,hb,hbunitary⟩ | ⟨b,hb,hbunitary⟩
  · exact Or.inl hree
  · exact Or.inr (Or.inl ⟨b,hb,hblinear,
      original_linear_factor_quadratic_degrees Q e h split hm 0 1 (by decide)
        hn hb hlinear hblinear⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,hb,hbunitary,
      original_linear_unitary_degree_bounds Q e h split hm 0 1 (by decide)
        hn hb hlinear (Or.inl hbunitary)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b,hb,hbunitary,
      original_linear_unitary_degree_bounds Q e h split hm 0 1 (by decide)
        hn hb hlinear (Or.inr hbunitary)⟩))

/-- The binary source endpoint leaves only binary (6H) data or a field-four
linear opposite factor. This includes the original nonperfect factors. -/
theorem original_binary_octagon_source_selection
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 2) :
    Nonempty (OriginalReeSixHData Q e split 1 0) ∨
      ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 4 := by
  rcases original_octagon_source_selection Q e h split hm (n := 1) (by decide)
      hlinear with ⟨m,⟨c⟩⟩ | ⟨b,hb,hmodel,hdegree⟩ |
      ⟨b,hb,hmodel,hparity,hupper,hlower⟩ | ⟨b,hb,hmodel,hparity,hupper,hlower⟩
  · have he := c.common_field
    have hmzero : m = 0 := by omega
    subst m
    exact Or.inl ⟨c⟩
  · have hbval : b = 2 := by rcases hdegree with hdegree | hdegree <;> omega
    subst b
    exact Or.inr hmodel
  · omega
  · omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.CompleteConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OctagonFactorAssembly

/-!
# Original factor data feeds the completed Section 10 comparison

The original factor theorem constructs the faithful panel quotients and their
whole-Borel maps on the same marked octagon.  This leaf extracts those maps
from the resulting `OriginalReeSixHData` and applies the completed Section 10
consumer.  Thus the final comparison no longer has a free panel-marking
premise: only the actual Fong--Seitz factor quotients remain as inputs.

Source: Fong--Seitz I (1973), (1J), (6H), pp. 6 and 51--56; Fong--Seitz II
(1974), Section 10.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)

include e h split hm hn in
/-- The proved original factor quotients feed the full Section 10 comparison.

The panel maps and Borel identities are extracted from the source-constructed
`OriginalReeSixHData`; no relation package, common-field equality, or model
comparison is assumed as an additional premise.
-/
theorem original_factor_concrete_comparison
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL2BinaryMatrixGroup n)
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup m) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
  obtain ⟨c, _⟩ := original_factor_sixH_data Q e h split hm n hn m μ₀ μ₁
  exact ReeSection10.original_concrete_comparison Q split e h hm n hn m
    c.originalLinear c.linearSylow c.originalLinearBorel
    c.originalSuzuki c.originalSuzukiBorel

include e h split hm hn in
/-- The actual linear/Suzuki or linear/dihedral factor alternatives feed the
completed comparison, including the full binary Ree parameter. -/
theorem original_suzuki_or_dihedral_concrete_comparison
    (hlinear : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n))
    (hother : (∃ a, Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃*
        SuzukiMatrixGroup a)) ∨
      Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5)) :
    ∃ m, Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
          inf_le_left inf_le_right)
        (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
  obtain ⟨m, ⟨c⟩⟩ := original_suzuki_or_dihedral_sixH_data Q e h split hm n hn
    hlinear hother
  exact ⟨m, ReeSection10.concrete_comparison_ofSixHData Q split e c.toReeSixHData⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

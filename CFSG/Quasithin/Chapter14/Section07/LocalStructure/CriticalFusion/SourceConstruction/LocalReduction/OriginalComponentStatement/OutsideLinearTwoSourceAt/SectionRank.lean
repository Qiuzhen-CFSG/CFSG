module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Rank comparison for the literal original local sections

An inclusion of original local groups includes their conjugate spans of
the same seed. Their coordinate kernels are the same original flag line.
Counting these exact sections therefore compares their binary dimensions,
without choosing a compatible complement or quotient splitting.
Source application: Aschbacher–Smith 14.7.42 and 14.7.46.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam
open scoped IsMulCommutative
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Inclusion of original local groups increases the rank of their literal
quotients by the same flag line. -/
theorem local_section_finrank_mono
    {I J : Subgroup G} (hJI : J ≤ I)
    [IsElementaryAbelian 2 (F.UH I)] [IsElementaryAbelian 2 (F.UH J)]
    (aI : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (aJ : LocalQuotientAction J (F.UH J) (F.Vi 1)) :
    Module.finrank (ZMod 2) (Additive ((F.UH J) ⧸ (F.Vi 1).subgroupOf (F.UH J))) ≤
      Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  have hU : F.UH J ≤ F.UH I := conjugateSpanBy_mono le_rfl hJI
  have hc := card_le_of_le hU
  rw [(localQuotientSection aJ).card_section,(localQuotientSection aI).card_section,
    Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive ((F.UH J) ⧸ (F.Vi 1).subgroupOf (F.UH J))),
    Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))),Nat.card_zmod,
    F.card 1 (by decide)] at hc
  have hp :
      2 ^ Module.finrank (ZMod 2) (Additive ((F.UH J) ⧸ (F.Vi 1).subgroupOf (F.UH J))) ≤
        2 ^ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
    omega
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt

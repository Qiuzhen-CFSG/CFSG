module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.ModelBounds
public import Theory.SpecificGroups.PSL2.SmallPrimeFourGroup.DihedralPairs

/-!
# The remaining diagonal four-group geometry

A pair of involutions generates the maximal low dihedral subgroup D. A
four-group with a diagonal automorphism and containing the second involution
must have an inner conjugate outside N_Aut(PSL₂)(D), with the conjugator fixing
that involution. This is an explicit outstanding geometric input. Its consumer
in FourGroupGeneration proves the full generation contract from this input;
the input is not asserted here.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9, used by Aschbacher--Smith K.2, printed p.453.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

/-- The remaining geometric input: move a diagonal four-group out of the
normalizer while fixing its prescribed inner involution. -/
@[expose] def FourGroupNormalizerEscape (F : Type) [Field F] [Finite F] (p : ℕ) : Prop :=
  ∀ (a b : PSL(2, F)), a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 →
    IsCoatom (closure ({a, b} : Set PSL(2, F))) →
    Nat.card (closure ({a, b} : Set PSL(2, F))) = Theory.PSL2.SmallPrimeFourGroup.lowOrder p →
    ∀ A : Subgroup (MulAut PSL(2, F)), IsElementaryAbelian 2 A → Nat.card A = 4 →
      (¬ A ≤ (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range) → MulAut.conj b ∈ A →
      ∃ x : PSL(2, F), x * b * x⁻¹ = b ∧
        ¬ A.map (MulAut.conj (MulAut.conj x)).toMonoidHom ≤
          normalizer ((closure ({a, b} : Set PSL(2, F))).map
            (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)) : Set (MulAut PSL(2, F)))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

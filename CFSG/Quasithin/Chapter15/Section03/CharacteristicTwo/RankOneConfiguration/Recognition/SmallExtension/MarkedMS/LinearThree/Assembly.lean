module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.BinaryReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

/-!
# Assembly of the earlier interface from the binary classification

The small central-core quotient forces the field degree to be one. Coefficient
transport then turns a binary classification into the full `linearThree` field
used by Chapter 15, including all five source alternatives and every section's
common marking. The independent rank-two implication is retained unchanged.

This is a conditional assembly theorem: the binary classification and the
rank-two implication must both be proved before it gives an earlier source
classification. Source: Aschbacher--Smith C.1.32 and C.1.34, pp.135--137.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u

/-- The exact universal source interface reduces to its binary linear-three
branch, with the separate C.1.32 input preserved as an explicit premise. -/
theorem EarlierMSClassifications.of_binary {κ : GroupClass.{u}}
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair κ L R → RankTwoAlternatives L R)
    (binary : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair κ L R →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          MSModuleAlternatives L R S 1 (ZMod 2) e) :
    EarlierMSClassifications κ := by
  refine ⟨rankTwo, ?_⟩
  intro J _ _ L R h n hn F _ _ hF he S hS hRS
  exact h.linearThree_of_binary n hn F hF he
    (fun e => binary J L R h e S hS hRS)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

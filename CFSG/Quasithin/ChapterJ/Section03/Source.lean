module
public import CFSG.Quasithin.ChapterJ.Section03.EarlierInputs
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.Suzuki
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.Middle
/-!
# The unconditional source theorems of Chapter J.3

The original TypeRu setup supplies its genuine local choices. The completed
J.2 producers now discharge the Suzuki centralizer, the two involution
classes, the exact480 middle-layer count, and the original three- and
five-subgroups. The source counting argument gives the full group order;
substituting it into the five-normalizer theorem completes J.3.6.

Source: Aschbacher--Smith J.3.1--6, printed pp.438--439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

theorem order_source (c : Choices d) : Nat.card G=2^14*3^3*5^3*7*13*29 := by
  obtain ⟨r⟩ := c.suzuki_source
  exact order_of_suzuki_and_middle_count c r (c.middle_z_class_card_source)

/-- The order of an arbitrary group satisfying the original TypeRu hypotheses. -/
theorem theorem_J_3_1 (h : IsTypeRu G) : Nat.card G=2^14*3^3*5^3*7*13*29 := by
  obtain ⟨d,⟨c⟩⟩ := SourceCompletion.local_choices_of_typeRu h
  exact order_source c

/-- The full original-source Sylow-five normalizer theorem. -/
theorem lemma_J_3_6 (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (fiveOddPart B5)=125 ∧ IsExtraspecial 5 (fiveOddPart B5) ∧
      (∃ S : Sylow 5 G, (S : Subgroup G)=fiveOddPart B5) ∧
      (Theory.GroupTheory.generalizedFitting (normalizer (B5Image B5 : Set G))).map
        (normalizer (B5Image B5 : Set G)).subtype=fiveOddPart B5 ∧
      ∃ R : Subgroup G, R≤d.toTypeRuSetup.H ∧ Disjoint (fiveOddPart B5) R ∧
        normalizer (B5Image B5 : Set G)=fiveOddPart B5⊔R ∧
        Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
        c.z∈(center R).map R.subtype :=
  ⟨SourceCompletion.five_oddPart_card c B5,lemma_J_3_6_of_order c B5 (order_source c)⟩

end CFSG.Quasithin.ChapterJ.Section03

module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsTwoLocal
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsHigmanSims

/-!
# The remaining sporadic maximal-overgroup obstruction

The proved six-carrier, Hall--Janko and Higman--Sims reductions leave J₄,
Held and Rudvalis. The two-local calculations now settle every Held and
Rudvalis full-Sylow overgroup lying in a subgroup with nontrivial two-core.
Consequently a remaining failure in either carrier produces an actual
maximal odd-index subgroup with trivial two-core.

The final theorem applies this deduction to precisely C/O∞(C), where C is
the original normalized overcomponent. This is checked progress toward the
A.3.12(17,19,20) input to 1.2.8(1), pp.47--48 and 506. The J₄ restriction
and exclusion of the displayed Held/Rudvalis maximal subgroups remain open;
this module does not assert the full sporadic uniqueness theorem.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

/-- The full sporadic predicate reduces to J₄, or a Held/Rudvalis maximal
odd-index subgroup with trivial two-core. All carrier alternatives are actual equivalences. -/
theorem sporadic_model_remaining_coreFree [IsSimpleGroup G] [Group.IsPerfect G]
    (hspor : ChapterA.Section02.IsTheoremCSporadicModel G)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    Nonempty (G ≃* Janko4.Model) ∨
      ((Nonempty (G ≃* Held.He) ∨ Nonempty (G ≃* Rudvalis.Model)) ∧
        ∃ (S : Sylow 2 G) (M : Subgroup G), IsCoatom M ∧ (S : Subgroup G) ≤ M ∧
          ¬ 2 ∣ M.index ∧ pCore 2 M = ⊥) := by
  obtain ⟨name,hn,iso⟩ := sporadic_model_remaining_after_higman_sims hspor hu
  rcases hn with rfl | rfl | rfl
  · exact Or.inl iso
  · exact Or.inr ⟨Or.inl iso,held_coreFree_maximal_of_not_unique iso hu⟩
  · exact Or.inr ⟨Or.inr iso,rudvalis_coreFree_maximal_of_not_unique iso hu⟩

/-- Apply the remaining maximal-overgroup obstruction to the literal radical
quotient of the original normalized overcomponent, without a new local premise. -/
theorem moved_normalized_remaining_sporadic_quotient_coreFree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ChapterA.Section02.IsTheoremCSporadicModel Q →
      Nonempty (Q ≃* Janko4.Model) ∨
        ((Nonempty (Q ≃* Held.He) ∨ Nonempty (Q ≃* Rudvalis.Model)) ∧
          ∃ (S : Sylow 2 Q) (M : Subgroup Q), IsCoatom M ∧ (S : Subgroup Q) ≤ M ∧
            ¬ 2 ∣ M.index ∧ pCore 2 M = ⊥) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact sporadic_model_remaining_coreFree hmodel hu

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality

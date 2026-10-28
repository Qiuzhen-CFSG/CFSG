module

public import CFSG.Quasithin.MainForward
public import CFSG.Quasithin.Chapter2.EmptyDelta

/-!
# The proved empty-delta branch in the forward reduction

The unique maximal two-local overgroup is selected from the actual `h211`
input of `forward_to_theoremD`. Empty delta is now discharged by the source
Bender theorem. The nonempty-delta branch of Chapter 2 and Theorem E remain
explicit, independent source obligations; this reduction is not the complete
forward classification.

Source: Aschbacher--Smith, Theorem 2.1.1, printed p.518, and the forward
proof of the Main Theorem, printed p.1166.
-/

public section
namespace CFSG.Quasithin.MainForward
open Subgroup Theory.GroupTheory ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The forward reduction with the empty-delta case of Chapter 2 discharged. -/
theorem forward_to_theoremD_of_nonempty_delta
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h211 : ∀ (T : Sylow 2 G) (M : Subgroup G),
      IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      (∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) →
      (Chapter2.delta (Chapter1.He G) M).Nonempty → IsTheorem211Model G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) :
    IsQTKEModelWithoutReeF4 G ∨
      ∃ T : Sylow 2 G,
        1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
        (faithfulLocalComponents T).Nonempty := by
  classical
  apply forward_to_theoremD h ?_ hE
  intro T huniq
  obtain ⟨M, ⟨hM, hTM⟩, hunique⟩ := huniq
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M :=
    fun N hn ht => hunique N ⟨hn, ht⟩
  by_cases hd : Chapter2.delta (Chapter1.He G) M = ∅
  · exact Chapter2.BenderFusion.theorem_2_1_1_of_delta_empty h T M hM hTM hu hd
  · exact h211 T M hM hTM hu (Set.nonempty_iff_ne_empty.mpr hd)

end CFSG.Quasithin.MainForward

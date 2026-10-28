module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.QuarticSylowSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.M22Center

/-!
# The exact surviving sporadic intersections

All seven discarded models, the M₁₁ and M₂₃ covering kernels, and the
quartic M₂₂ kernel are eliminated by the concrete source calculations.
The direct survivors have their actual centralizer, hexad or heptad
intersection. The one remaining cover is recorded explicitly as the binary
M₂₂ cover; it is not silently identified with M₂₂.

Source: Aschbacher--Smith 2.3.9(7)(d,f), printed pp.525--526.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu ClassificationModels
open scoped Pointwise
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The completed direct sporadic alternatives of 2.3.9(7), retaining the
literal subgroup image defining each Mathieu geometry. -/
def SporadicIntersection (L M : Subgroup G) (z : G) : Prop :=
  (Nonempty (L ≃* M11) ∧ ∃ t : L, orderOf t = 2 ∧
    IsConjugationProjection L z t ∧
    L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G)) ∨
  (∃ e : L ≃* M22,
    (∃ B ∈ m22Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M22 B) ∧
    AlternatingBySixteen (M.subgroupOf L) 6) ∨
  (∃ e : L ≃* M23,
    (∃ B ∈ m23Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M23 B) ∧
    AlternatingBySixteen (M.subgroupOf L) 7)

/-- Exactly one central-cover branch remains after all existing sporadic
source calculations. The kernel here is the original O₂(L). -/
theorem LocalSetup.sporadic_intersection_or_binary_cover
    (h : LocalSetup H L M S z) {name : SporadicName}
    (d : SporadicQuotientInput L z name) (hn : name ≠ .j3) :
    SporadicIntersection L M z ∨
      (name = .m22 ∧ Nat.card (pCore 2 L) = 2 ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* M22)) := by
  rcases h.sporadic_name_cases d hn with rfl | rfl | rfl
  · obtain ⟨_,e,_,hi⟩ := mathieuEleven_cover_intersection h d
    exact .inl (.inl ⟨⟨e⟩, hi⟩)
  · rcases h.mathieuTwentyTwo_core_card_cases d.quotientIso with hk | hk | hk
    · obtain ⟨e,_,hi,hshape⟩ := mathieuTwentyTwo_cover_intersection_of_core_eq_bot h d hk
      exact .inl (.inr (.inl ⟨e,hi,hshape⟩))
    · exact .inr ⟨rfl,hk,⟨d.quotientIso⟩⟩
    · exact (h.mathieuTwentyTwo_quartic_false d hk).elim
  · obtain ⟨_,e,_,hi,hshape⟩ := mathieuTwentyThree_cover_intersection h d
    exact .inl (.inr (.inr ⟨e,hi,hshape⟩))

/-- In the original Γ₀ configuration the binary residual further forces
the selected ambient Sylow center to be cyclic. Structural 1.1.5 is proved;
only the independent earlier local-C implication remains explicit. -/
theorem MathieuSourceSetup.sporadic_intersection_or_binary_cover [Finite G]
    {C : GroupClass} (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE C G) (sourceC : LocalC129Input C G)
    {name : SporadicName} (d : SporadicQuotientInput L z name) (hn : name ≠ .j3) :
    SporadicIntersection L M z ∨
      (name = .m22 ∧ Nat.card (pCore 2 L) = 2 ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* M22) ∧ IsCyclic (center (c.T : Subgroup G))) := by
  rcases (c.localSetup hG structural115Input sourceC).sporadic_intersection_or_binary_cover d hn
      with hi | ⟨hn,hk,⟨e⟩⟩
  · exact .inl hi
  · exact .inr ⟨hn,hk,⟨e⟩,c.mathieuTwentyTwo_ambient_center_isCyclic hG sourceC e⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

module
public import Theory.GroupTheory.MinimalParabolicGeneration

/-!
# Refining a specified overgroup cover by minimal parabolics

Given a family of overgroups of X, retain the nonnormal unique-maximal
overgroups of X lying in at least one member. McBride's finite-lattice
argument, applied inside each member, shows that this refinement and N(X)
generate the same subgroup as the original family and N(X).

In particular, properties inherited by subgroups, such as solvability,
need only be checked on the original cover, not on every minimal parabolic.
Source: Aschbacher--Smith B.6.3--4, printed pp.112--113; application in
the model-generation step of 10.3.3, printed p.756.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- McBride refinement inside a specified overgroup family, with the original
normalizer retained. The case X itself belongs to the cover is included. -/
theorem refined_nonNormalUniqueMaximal_sup_normalizer
    (X : Subgroup G) (Γ : Set (Subgroup G))
    (hΓ : ∀ H ∈ Γ, X ≤ H) :
    sSup {P : Subgroup G | P ∈ nonNormalUniqueMaximalOvergroups X ∧
        ∃ H ∈ Γ, P ≤ H} ⊔ normalizer (X : Set G) =
      sSup Γ ⊔ normalizer (X : Set G) := by
  apply le_antisymm
  · apply sup_le_sup_right
    apply sSup_le
    rintro P ⟨_, H, hH, hPH⟩
    exact hPH.trans (le_sSup hH)
  · apply sup_le _ le_sup_right
    apply sSup_le
    intro H hH
    by_cases he : X = H
    · rw [← he]
      exact X.le_normalizer.trans le_sup_right
    · have hx : X < H := lt_of_le_of_ne (hΓ H hH) he
      rw [Order.eq_sSup_hasUniqueMaximalOver hx]
      apply sSup_le
      rintro P ⟨hPH, hP⟩
      by_cases hn : P ≤ normalizer (X : Set G)
      · exact hn.trans le_sup_right
      · exact (le_sSup (show P ∈ {P : Subgroup G |
          P ∈ nonNormalUniqueMaximalOvergroups X ∧ ∃ H ∈ Γ, P ≤ H} from
          ⟨⟨hP, hn⟩, H, hH, hPH⟩)).trans le_sup_left

end Subgroup

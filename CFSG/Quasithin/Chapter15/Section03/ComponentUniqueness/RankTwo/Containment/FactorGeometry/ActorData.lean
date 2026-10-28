module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.Residuals

/-!
# The plane actors to be constructed for 15.3.39--40

This is an output interface for the local action calculation. The left actor
is the literal two-residual of C_{Y₊}(V₂). The right actor must be constructed
inside Y₊ ∩ C_M(V₁); in case (2) it need not be the full two-residual of that
intersection. Both actors have three-part three and generate Y₊.

The elementary consequences below derive nontriviality, relative normality,
and invariance from this output and normalization of the planes. The natural
orthogonal action and the rank-two quotient must still construct the output.
In particular this module makes no source containment assertion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.39--40,
printed pp.1137--1138, with Mᵢ = C_M(V_{3-i}) on printed p.1122.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

/-- Conclusion data for the rank-two local action calculation. No theorem
asserts its existence here. The V₁-generation clause is conditional on Y₊ = Y. -/
structure PlaneActorPair (M Y Yplus S V V₁ V₂ : Subgroup G) where
  right : Subgroup G
  right_le : right ≤ Yplus ⊓ (M ⊓ centralizer (V₁ : Set G))
  right_normal : (right.subgroupOf Yplus).Normal
  right_invariant : S ≤ normalizer (right : Set G)
  right_perfect : IsPPerfect 2 right
  right_three_part : 3 ^ (Nat.card right).factorization 3 = 3
  left_three_part : 3 ^ (Nat.card (centralizingFactor Yplus V₂)).factorization 3 = 3
  generate : Yplus = centralizingFactor Yplus V₂ ⊔ right
  plane : ⁅V, right⁆ = V₂
  plane_self : ⁅V₂, right⁆ = V₂
  other_plane : Yplus = Y → ⁅V₁, centralizingFactor Yplus V₂⁆ = V₁

private theorem ne_bot_of_three_part {X : Subgroup G}
    (h : 3 ^ (Nat.card X).factorization 3 = 3) : X ≠ ⊥ := by
  rintro rfl
  norm_num at h

/-- Both selected actors are nontrivial, from their exact three-parts. -/
theorem PlaneActorPair.nontrivial {M Y Yplus S V V₁ V₂ : Subgroup G}
    (a : PlaneActorPair M Y Yplus S V V₁ V₂) :
    centralizingFactor Yplus V₂ ≠ ⊥ ∧ a.right ≠ ⊥ :=
  ⟨ne_bot_of_three_part a.left_three_part, ne_bot_of_three_part a.right_three_part⟩

/-- Left-actor normality and S-invariance use only invariance of Y₊ and V₂. -/
theorem plane_left_actor_normal_invariant [Finite G] {Yplus S V₂ : Subgroup G}
    (hYV : Yplus ≤ normalizer (V₂ : Set G))
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hSV : S ≤ normalizer (V₂ : Set G)) :
    ((centralizingFactor Yplus V₂).subgroupOf Yplus).Normal ∧
      S ≤ normalizer (centralizingFactor Yplus V₂ : Set G) :=
  ⟨centralizingFactor_normal hYV, normalizes_centralizingFactor hSY hSV⟩

/-- The generated plane lies in Y₊ because V normalizes Y₊. -/
theorem PlaneActorPair.plane_le {M Y Yplus S V V₁ V₂ : Subgroup G}
    (a : PlaneActorPair M Y Yplus S V V₁ V₂)
    (hVY : V ≤ normalizer (Yplus : Set G)) : V₂ ≤ Yplus := by
  rw [← a.plane]
  exact (commutator_mono le_rfl (a.right_le.trans inf_le_left)).trans
    (le_normalizer_iff_commutator_le_right.mp hVY)

end CFSG.Quasithin.Chapter15.Section03.RankTwo

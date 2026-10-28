module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Restriction of best offenders

The image on a noncentralized invariant subspace is again a best offender,
and equal-weight minimality descends. The proof lifts every image subgroup
through the actual action kernel and cancels its rank in the fixed-space
comparison. Equality yields equal weight in the original representation and
the exact fixed-space sum. Applying this to the kernel proves the faithful
span or nontrivial equal-weight offender alternative; minimality excludes
the second branch.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.7.1, printed pp. 118–119 (1 March 2004 manuscript).
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

/-- The source comparison for every subgroup containing the pointwise kernel. -/
theorem IsBestOffender.image_weight_comparison {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hBA : B ≤ A) (hKB : subspaceKernel ρ W A ≤ B) :
    weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W B) +
        (Module.finrank (ZMod 2) (fixedSpace ρ B) -
          Module.finrank (ZMod 2)
            (fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) : Submodule (ZMod 2) V)) ≤
      weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hpA := IsElementaryAbelian.isPGroup 2 A
  have hpB := hpA.of_injective (Subgroup.inclusion hBA) (Subgroup.inclusion_injective hBA)
  have hrA := rank_subspaceKernel_add_image ρ W A hW hpA
  have hrB := rank_subspaceKernel_add_image ρ W B (hBA.trans hW) hpB
  rw [subspaceKernel_eq_of_le ρ W hBA hKB] at hrB
  have hdA := (restrictedFixedSpaceEquiv ρ W A hW).finrank_eq
  have hdB := (restrictedFixedSpaceEquiv ρ W B (hBA.trans hW)).finrank_eq
  have hc := hA.restriction_comparison ρ hBA W
  unfold weight
  omega

/-- Best-offender weight is maximal on the restricted image. -/
theorem IsBestOffender.image_weight_le {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hBA : B ≤ A) (hKB : subspaceKernel ρ W A ≤ B) :
    weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W B) ≤
      weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  have := hA.image_weight_comparison ρ W hW hBA hKB
  omega

/-- Equality on the image forces the two exact equalities in B.7.1. -/
theorem IsBestOffender.image_weight_eq_iff {A B : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hBA : B ≤ A) (hKB : subspaceKernel ρ W A ≤ B) :
    weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W B) =
      weight (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ↔
    EqualWeightLE ρ B A ∧ fixedSpace ρ A ⊔ (W ⊓ fixedSpace ρ B) = fixedSpace ρ B := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hpA := IsElementaryAbelian.isPGroup 2 A
  have hpB := hpA.of_injective (Subgroup.inclusion hBA) (Subgroup.inclusion_injective hBA)
  have hrA := rank_subspaceKernel_add_image ρ W A hW hpA
  have hrB := rank_subspaceKernel_add_image ρ W B (hBA.trans hW) hpB
  rw [subspaceKernel_eq_of_le ρ W hBA hKB] at hrB
  have hdA := (restrictedFixedSpaceEquiv ρ W A hW).finrank_eq
  have hdB := (restrictedFixedSpaceEquiv ρ W B (hBA.trans hW)).finrank_eq
  rw [← hA.restriction_weight_eq_iff ρ hBA W]
  unfold weight
  omega

/-- Restriction to a noncentralized invariant subspace preserves best offenders. -/
theorem IsBestOffender.restricted {A : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A) :
    IsBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  refine ⟨hA.1.restrictedSubgroup ρ W hW hn, ?_⟩
  intro D hD
  obtain ⟨B, hBA, hKB, hBD⟩ := exists_subgroup_restrictedSubgroup ρ W hW D hD
  rw [← hBD]
  exact hA.image_weight_le ρ W hW hBA hKB

/-- Equal-weight minimality descends to the faithful action image. -/
theorem IsMinimalBestOffender.restricted {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A) :
    IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  refine ⟨hA.1.restricted ρ W hW hn, ?_⟩
  intro D hDbest hDA
  obtain ⟨B, hBA, hKB, hBD⟩ := exists_subgroup_restrictedSubgroup ρ W hW D hDA.1
  have hBne : B ≠ ⊥ := by
    intro hB
    apply hDbest.1.1
    rw [← hBD, hB, restrictedSubgroup_bot]
  have heq := ((hA.1.image_weight_eq_iff ρ W hW hBA hKB).mp
    (by rw [hBD]; exact hDA.2)).1
  have hBBest := hA.1.of_equalWeightLE ρ (hA.1.1.of_le hBA hBne) heq
  have hBeq := hA.2 B hBBest heq
  rw [← hBD, hBeq]

/-- At ratio one, the actual kernel has equal weight and its fixed space is the source sum. -/
theorem IsBestOffender.kernel_equalWeight_of_image_rank_eq {A : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    EqualWeightLE ρ (subspaceKernel ρ W A) A ∧
      fixedSpace ρ A ⊔ W = fixedSpace ρ (subspaceKernel ρ W A) := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hr := rank_subspaceKernel_add_image ρ W A hW (IsElementaryAbelian.isPGroup 2 A)
  have hd := (restrictedFixedSpaceEquiv ρ W A hW).finrank_eq
  have hc := fixedCodim_add_finrank (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)
  have hi : W ⊓ fixedSpace ρ (subspaceKernel ρ W A) = W :=
    inf_eq_left.mpr (le_fixedSpace_subspaceKernel ρ W A)
  have h := (hA.restriction_weight_eq_iff ρ (subspaceKernel_le ρ W A) W).mp
    (by rw [hi]; omega)
  simpa only [hi] using h

/-- B.7.1(3): the kernel is trivial and spans with the fixed space, or is an equal-weight offender. -/
theorem IsBestOffender.restriction_alternatives {A : Subgroup G}
    (hA : IsBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    (subspaceKernel ρ W A = ⊥ ∧ W ⊔ fixedSpace ρ A = ⊤) ∨
    (subspaceKernel ρ W A ≠ ⊥ ∧ IsBestOffender ρ (subspaceKernel ρ W A) ∧
      EqualWeightLE ρ (subspaceKernel ρ W A) A) := by
  obtain ⟨hweight, hsum⟩ := hA.kernel_equalWeight_of_image_rank_eq ρ W hW heq
  by_cases hK : subspaceKernel ρ W A = ⊥
  · refine Or.inl ⟨hK, ?_⟩
    simpa only [hK, fixedSpace_bot, sup_comm] using hsum
  · exact Or.inr ⟨hK, hA.of_equalWeightLE ρ
      (hA.1.of_le (subspaceKernel_le ρ W A) hK) hweight, hweight⟩

/-- Minimality excludes the proper nontrivial kernel alternative. -/
theorem IsMinimalBestOffender.faithful_span_of_image_rank_eq {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A)
    (heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    subspaceKernel ρ W A = ⊥ ∧ W ⊔ fixedSpace ρ A = ⊤ := by
  rcases hA.1.restriction_alternatives ρ W hW heq with h | ⟨_, hbest, hweight⟩
  · exact h
  · exact (subspaceKernel_ne_self ρ W hn (hA.2 _ hbest hweight)).elim

/-- The non-strong case in B.1.5(2). -/
theorem IsMinimalBestOffender.faithful_span_of_not_strong {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A)
    (hns : ¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    subspaceKernel ρ W A = ⊥ ∧ W ⊔ fixedSpace ρ A = ⊤ := by
  have hbest := hA.1.restricted ρ W hW hn
  apply hA.faithful_span_of_image_rank_eq ρ W hW hn
  have hoff := (hbest.isOffender _).2
  have hnot : ¬ fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) <
      rank (restrictedSubgroup ρ W A) := fun h => hns ⟨hbest.1, h⟩
  omega

end Representation.BinaryOffender

module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.Borel
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.ModelActors

/-!
# Finite images of the tensor actors

The component image is the marked 1 × A₅, and the actual Borel image is A₄.
Thus both residual actors belong to the source family and are distinct. The
exhaustive finite-model actor calculation excludes mixed and diagonal images.
Kernel containment from the source Sylow subgroup then recovers the literal
pair family upstairs, with no additional classification or Borel premise.

The final theorem establishes the group-theoretic clause of
Aschbacher–Smith 14.4.10(1), printed p.1010, using the actual models in
14.4.2(5), printed p.1006 (combined 1 March 2004 manuscript). The tensor
geometry and the remaining clauses belong to the common-branch assembly.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G]

/-- Both actual residual actors belong to X and are distinct, from the source
Sylow subgroup and either specified quotient model. -/
theorem first_second_mem_X_and_distinct {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive)) :
    first H ∈ XFamily H T ∧ second H T ∈ XFamily H T ∧ first H ≠ second H T := by
  have hT : T ≤ H := hP ▸ map_subtype_le _
  obtain ⟨eB⟩ := exists_star_borel_equiv P hP hmodel
  exact ⟨first_mem_X hT hmodel, second_mem_X_of_borel_equiv hT eB,
    first_ne_second_of_borel_equiv hmodel eB⟩

/-- Application of an exhaustive model calculation to the literal source family.
Only the finite-model actor classification remains an explicit premise;
the component, Borel, Sylow, kernel and lifting identifications are proved. -/
theorem family_eq_pair_of_model_actors {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive))
    (hactors : ∀ (Q : Sylow 2 (coreQuotient H)) (A : Subgroup (coreQuotient H)),
      (Q : Subgroup (coreQuotient H)) ≤ normalizer (A : Set _) →
      IsPPerfect 2 A → Nat.card (A ⧸ pCore 2 A) = 3 →
      A = pCore 3 (coreQuotient H) ∨ A = solvableResidual (coreQuotient H) ⊓
        normalizer (((Q : Subgroup (coreQuotient H)) ⊓ solvableResidual (coreQuotient H) :
          Subgroup (coreQuotient H)) : Set _)) :
    XFamily H T = {first H, second H T} ∧ first H ≠ second H T := by
  have hT : T ≤ H := hP ▸ map_subtype_le _
  obtain ⟨eB⟩ := exists_star_borel_equiv P hP hmodel
  obtain ⟨Q, hQ⟩ := exists_star_sylow P hP
  apply family_eq_pair_of_borel_images hT (twoCore_le_of_sylow P hP) hmodel eB
  intro X hX
  have hnorm : (Q : Subgroup (coreQuotient H)) ≤ normalizer (star H X : Set _) := by
    rw [hQ]
    exact (star_mem_X hX).T_normalizes
  rcases hactors Q (star H X) hnorm
    (isPPerfect_of_residual_eq (star_mem_X hX).residual_eq)
    (star_quotient_card_three hX) with he | he
  · exact Or.inl he
  · rw [hQ, ← star_component H, ← star_borel_eq_relative_normalizer P hP] at he
    exact Or.inr he

/-- The literal family in 14.4.10(1) consists of the two distinct residual
actors. The source Sylow subgroup and either actual quotient model suffice:
the component image, Borel identification and exhaustive actor classification
are all proved, including exclusion of mixed and diagonal images. -/
theorem family_eq_pair_of_model {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive)) :
    XFamily H T = {first H, second H T} ∧ first H ≠ second H T :=
  family_eq_pair_of_model_actors P hP hmodel
    (Theory.SpecificGroups.TensorThreeFiveActors.model_actors hmodel)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end

module
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Stellmacher.BaumannNormalizer
/-!
# A common local overgroup from the residual Sylow condition

The original common-normal theorem applied to the normalizer of R and an
H-star overgroup supplies a nontrivial two-subgroup normal in their join.
Its normalizer lies in a maximal two-local overgroup, giving a common
ambient group without any component embedding classification.

Source: Aschbacher–Smith 3.1.1 and the natural case of 10.2.2(4).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G]
theorem HStar.normalizer_residual_sylow_common_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ HStar (T : Subgroup G) M)
    (R : Subgroup G) (hne : R ≠ ⊥) (hRT : R ≤ (T : Subgroup G))
    (hTN : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hs : Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R)) :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      normalizer (R : Set G) ⊔ H ≤ M₁ := by
  have hp : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hA : normalizer (R : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨R,hne,hp,rfl⟩,hTN⟩
  obtain ⟨Q,hQR,hQ,hQN⟩ := source_common_normal_knownSimple hG T
    (normalizer (R : Set G)) H R hA hH.1.1
    (HStar.hasUniqueMaximalOver T hTM hH) hne hRT hs le_rfl
  have hloc : IsTwoLocal (normalizer (Q : Set G)) :=
    ⟨Q,hQ,hp.to_le hQR,rfl⟩
  obtain ⟨M₁,hNM,hmax⟩ := Finite.exists_le_maximal hloc
  refine ⟨M₁,hmax,?_⟩
  have hle := (normalIn_iff_le_normalizer.mp hQN).2
  rw [generated_eq_sup] at hle
  exact hle.trans hNM
end CFSG.Quasithin.Chapter3

module
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Mathlib.GroupTheory.Subgroup.Simple
/-!
# Commutator generation above a centerless simple quotient

If a p-perfect group maps onto a centerless simple group through a p-group
kernel, every subgroup escaping that kernel generates the whole group by
commutators. Its image has a nonzero normal commutator in the simple quotient;
p-perfectness then removes the remaining p-group quotient upstairs.

This applies to the cubic torus of a natural A₅ block without a splitting or
central-cover hypothesis.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G F : Type*} [Group G] [Group F] {p : ℕ} [Fact p.Prime]

/-- An actual subgroup escaping the p-kernel moves the whole p-perfect group. -/
theorem commutator_top_eq_of_pPerfect_simple_quotient (hG : IsPPerfect p G) (f : G →* F)
    (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    [IsSimpleGroup F] (hz : center F = ⊥) (D : Subgroup G) (hD : ¬ D ≤ f.ker) :
    ⁅(⊤ : Subgroup G),D⁆ = ⊤ := by
  have hnon : ⁅(⊤ : Subgroup F),D.map f⁆ ≠ ⊥ := by
    intro he
    have hd : D.map f ≤ center F := by
      rw [commutator_comm] at he
      simpa only [centralizer_univ, coe_top] using commutator_eq_bot_iff_le_centralizer.mp he
    rw [hz] at hd
    exact hD ((map_le_iff_le_comap).mp hd)
  let : (⁅(⊤ : Subgroup F),D.map f⁆).Normal :=
    normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left ⊤ (D.map f)))
  have ht : ⁅(⊤ : Subgroup F),D.map f⁆ = ⊤ :=
    (inferInstance : (⁅(⊤ : Subgroup F),D.map f⁆).Normal).eq_bot_or_eq_top.resolve_left hnon
  have hp : IsPPerfect p (⊤ : Subgroup G) :=
    hG.of_surjective (topEquiv.symm : G ≃* (⊤ : Subgroup G)).toMonoidHom topEquiv.symm.surjective
  apply (eq_commutator_of_isPPerfect_of_map_eq ⊤ D hp le_normalizer_of_normal f hk ?_).symm
  rw [map_top_of_surjective f hf,ht]
end Theory.GroupTheory

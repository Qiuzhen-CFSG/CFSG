module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Normal subgroups of two-perfect covers of A₄

In a two-perfect group mapping onto A₄ with two-group kernel, every
proper normal subgroup is a two-group. The image is either trivial,
Klein four, or all A₄; in the last case two-perfection kills the remaining
two-group quotient. The statement keeps the supplied homomorphism.
Source application: Aschbacher--Smith, completion of 12.3.1, p.811.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.Alternating
variable {H : Type*} [Group H]

theorem normal_eq_top_of_four_quotient_not_twoGroup
    (q : H →* alternatingGroup (Fin 4)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hp : IsPPerfect 2 H)
    (N : Subgroup H) [N.Normal] (hN : ¬ IsPGroup 2 N) : N = ⊤ := by
  let : (N.map q).Normal := Normal.map inferInstance q hq
  have himage : N.map q = ⊤ := by
    rcases AlternatingFourPair.normalA4 (N.map q) with hz | hz | hz
    · apply False.elim
      apply hN
      have hpre := (show IsPGroup 2 (N.map q) by rw [hz]; exact IsPGroup.of_bot).comap_of_ker_isPGroup q hk
      exact hpre.to_le (le_comap_map q N)
    · apply False.elim
      apply hN
      have hpre := (show IsPGroup 2 (N.map q) by
        rw [hz]
        change IsPGroup 2 (alternatingGroup.kleinFour (Fin 4))
        rw [← AlternatingFourPair.twoCore_eq_kleinFour]; exact pCore_isPGroup).comap_of_ker_isPGroup q hk
      exact hpre.to_le (le_comap_map q N)
    · exact hz
  apply top_unique
  apply isPPerfect_le_of_map_le_of_kernel_normalizes q ⊤ N
    (hp.of_surjective (topEquiv : (⊤ : Subgroup H) ≃* H).symm.toMonoidHom
      (topEquiv : (⊤ : Subgroup H) ≃* H).symm.surjective) hk le_normalizer_of_normal
  rw [himage]
  exact le_top
end Theory.SpecificGroups.Alternating

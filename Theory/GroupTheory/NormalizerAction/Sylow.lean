module

public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow images in the normalizer action

If an ambient Sylow subgroup normalizes K, its image is Sylow in the literal
quotient N(K)/C(K). The component image is normal there, so intersecting
gives a Sylow of K*. Odd prime rank at most one also passes to K*: cyclic
Sylow subgroups survive the actual surjection, including central covers.

Source: Aschbacher–Smith, A.2.7(1) and proof of 13.6.6, printed p.927.
-/

@[expose] public section
namespace Subgroup.NormalizerAction
open Subgroup
variable {H : Type*} [Group H] (K : Subgroup H)

instance componentImage_normal : (componentImage K).Normal :=
  Subgroup.Normal.map inferInstance (quotient K) (QuotientGroup.mk'_surjective (C K))

variable [Finite H] {p : ℕ} [Fact p.Prime]

/-- The normalizing Sylow maps to a Sylow in the faithful action quotient. -/
theorem exists_sylow_image (S : Sylow p H)
    (hSN : (S : Subgroup H) ≤ normalizer (K : Set H)) :
    ∃ P : Sylow p (Star K), (P : Subgroup (Star K)) = sylowImage K S := by
  exact ⟨(S.subtype hSN).mapSurjective (QuotientGroup.mk'_surjective (C K)), rfl⟩

/-- Retain the actual intersection T* ∩ K* as an embedded Sylow of K*. -/
theorem exists_component_sylow (S : Sylow p H)
    (hSN : (S : Subgroup H) ≤ normalizer (K : Set H)) :
    ∃ P : Sylow p (componentImage K),
      (P : Subgroup (componentImage K)).map (componentImage K).subtype =
        sylowImage K S ⊓ componentImage K := by
  obtain ⟨Q, hQ⟩ := exists_sylow_image K S hSN
  obtain ⟨P, hP⟩ := Q.exists_subgroupOf_eq_of_normal (componentImage K)
  refine ⟨P, ?_⟩
  rw [hP, hQ, subgroupOf_map_subtype]

/-- The rank-one quotient step does not assert general rank invariance
under central quotients. It uses the odd-prime cyclic Sylow theorem. -/
theorem componentImage_rank_le_one (hp : Odd p) (hr : primeRank p K ≤ 1) :
    primeRank p (componentImage K) ≤ 1 := by
  let P : Sylow p K := Classical.choice inferInstance
  let f : K →* componentImage K :=
    ((MulEquiv.subgroupCongr (componentMap_range K)).toMonoidHom).comp
      (componentMap K).rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr (componentMap_range K)).surjective.comp
      (componentMap K).rangeRestrict_surjective
  exact P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one hp hr) f hf

end Subgroup.NormalizerAction

module

public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.AutomizerTwoSubgroup

/-!
# Descending a three-weight torus action through a central quotient

Suppose a central quotient identifies the normalizer and centralizer of A
with the inverse images of those of B. An abelian centralizer of A descends
to an abelian centralizer of B. If A's automizer embeds in S₃, any normalizing
two-subgroup downstairs has centralizer index dividing two: lift the
two-subgroup through the odd central kernel and compare the relative indices
using the surjective restriction of the quotient map.

Source: the projective step in Aschbacher–Smith, A.3.21(c), pp.55–56,
and its use in the Cartan argument, pp.510–511.
-/

namespace Subgroup

/-- Descend the abelian centralizer and the two-subgroup action bound. -/
public theorem centralizer_two_action_of_central_coprime_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (A : Subgroup G) (B T : Subgroup H)
    (hN : (normalizer (B : Set H)).comap f = normalizer (A : Set G))
    (hC : (centralizer (B : Set H)).comap f = centralizer (A : Set G))
    [IsMulCommutative (centralizer (A : Set G))]
    (j : A.normalizerMonoidHom.range →* Equiv.Perm (Fin 3))
    (hj : Function.Injective j)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (B : Set H)) :
    IsMulCommutative ((centralizer (B : Set H)).subgroupOf T) ∧
      ((centralizer (B : Set H)).subgroupOf T).index ∣ 2 := by
  let _ : Finite H := Finite.of_surjective f hf
  have hCm : (centralizer (A : Set G)).map f = centralizer (B : Set H) := by
    rw [← hC, map_comap_eq_self_of_surjective hf]
  let _ : IsMulCommutative (centralizer (B : Set H)) := by
    rw [← hCm]
    exact map_isMulCommutative _ _
  refine ⟨subgroupOf_isMulCommutative _ _, ?_⟩
  obtain ⟨Q, hQ, hQmap, _, _, _⟩ :=
    exists_prime_lift_of_central_coprime f hf hcentral hker T hT
  have hQn : Q ≤ normalizer (A : Set G) := by
    rw [← hN]
    exact (map_le_iff_le_comap.mp (hQmap ▸ hn))
  have hindex := centralizer_subgroupOf_index_dvd_two_of_automizer A Q hQ hQn j hj
  let u : Q →* T := (MulEquiv.subgroupCongr hQmap).toMonoidHom.comp (f.subgroupMap Q)
  have hu : Function.Surjective u :=
    (MulEquiv.subgroupCongr hQmap).surjective.comp (f.subgroupMap_surjective Q)
  have he : ((centralizer (B : Set H)).subgroupOf T).comap u =
      (centralizer (A : Set G)).subgroupOf Q := by
    ext x
    change (x : G) ∈ (centralizer (B : Set H)).comap f ↔ _
    rw [hC]
    rfl
  rwa [← he, index_comap_of_surjective _ hu] at hindex

end Subgroup

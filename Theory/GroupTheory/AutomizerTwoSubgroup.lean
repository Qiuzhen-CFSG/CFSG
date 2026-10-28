module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finite.Perm

/-!
# Two-subgroups acting through a degree-three permutation group

If the induced automizer of B embeds in S₃, a normalizing two-subgroup T
has centralizer of index dividing two. Restrict the conjugation homomorphism
to T: its kernel is the relative centralizer, and its image has two-power
order dividing six.

This is the relative-index consequence of Aschbacher–Smith, A.3.21(c),
`refs/quasithin.pdf`, printed pp.55–56.
-/

namespace Subgroup

/-- A two-subgroup inducing permutations of three letters has centralizer
index at most two. Normalization is relative to this two-subgroup. -/
public theorem centralizer_subgroupOf_index_dvd_two_of_automizer {G : Type*} [Group G] [Finite G] (B T : Subgroup G)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (B : Set G))
    (j : B.normalizerMonoidHom.range →* Equiv.Perm (Fin 3))
    (hj : Function.Injective j) :
    ((centralizer (B : Set G)).subgroupOf T).index ∣ 2 := by
  let f := (j.comp B.normalizerMonoidHom.rangeRestrict).comp (inclusion hn)
  have hk : f.ker = (centralizer (B : Set G)).subgroupOf T := by
    ext t
    change j (B.normalizerMonoidHom.rangeRestrict (inclusion hn t)) = 1 ↔ _
    rw [← j.map_one, hj.eq_iff]
    rw [Subtype.ext_iff]
    change B.normalizerMonoidHom (inclusion hn t) = 1 ↔ _
    change inclusion hn t ∈ B.normalizerMonoidHom.ker ↔ _
    rw [B.normalizerMonoidHom_ker]
    rfl
  rw [← hk, index_ker]
  have hP := hT.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hd := card_subgroup_dvd_card f.range
  have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hs, ha] at hd
  rw [ha]
  exact (show Nat.Coprime (2 ^ a) 3 from (by decide : Nat.Coprime 2 3).pow_left a).dvd_of_dvd_mul_left hd

end Subgroup

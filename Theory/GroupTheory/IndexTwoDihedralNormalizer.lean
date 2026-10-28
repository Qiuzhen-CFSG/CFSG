module
public import Theory.GroupTheory.SpecificGroups.OddDihedralTwoNormalizer
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.SelfNormalizing
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.IndexTwoNormalizer

/-!
# Normalizers above an index-two dihedral product

A direct product of two odd dihedral groups has self-normalizing Sylow
two-subgroups. This property lifts through a two-group kernel. If such a
kernel quotient describes a subgroup of index two, the normalizer of its
intersection with the ambient Sylow is the ambient Sylow itself: the
nontrivial coset already has a representative in that Sylow.

These finite-group arguments supply the H-normalizer calculation in
Aschbacher--Smith, 14.6.16, printed p.1035 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

private theorem self_normalizing_dihedral (n : ℕ) (hn : Odd n)
    (e : G ≃* DihedralGroup n) (P : Sylow 2 G) :
    normalizer (P : Set G) = P := by
  apply odd_dihedral_two_subgroup_normalizer n hn e _ P.isPGroup'
  apply P.ne_bot_of_dvd_card
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact dvd_mul_right 2 n

private theorem self_normalizing_prod {K : Type*} [Group K] [Finite K]
    (hG : ∀ P : Sylow 2 G, normalizer (P : Set G) = P)
    (hK : ∀ P : Sylow 2 K, normalizer (P : Set K) = P)
    (P : Sylow 2 (G × K)) : normalizer (P : Set (G × K)) = P := by
  let A := P.mapSurjective (f := MonoidHom.fst G K) (fun x => ⟨(x,1),rfl⟩)
  let B := P.mapSurjective (f := MonoidHom.snd G K) (fun x => ⟨(1,x),rfl⟩)
  have hN : normalizer (P : Set (G × K)) ≤ (A : Subgroup G).prod (B : Subgroup K) := by
    intro x hx
    constructor
    · rw [← hG A]
      exact (P : Subgroup (G × K)).le_normalizer_map _ (mem_map_of_mem _ hx)
    · rw [← hK B]
      exact (P : Subgroup (G × K)).le_normalizer_map _ (mem_map_of_mem _ hx)
  have hp : IsPGroup 2 ((A : Subgroup G).prod (B : Subgroup K)) := by
    obtain ⟨a,ha⟩ := A.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := B.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  exact P.is_maximal' (hp.to_le hN) P.le_normalizer

/-- The quotient actors in a disjoint commuting pair of odd dihedral groups
have self-normalizing Sylow two-subgroups. -/
theorem self_normalizing_dihedral_join (A B : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (n : ℕ) (hn : Odd n)
    (eA : A ≃* DihedralGroup n) (eB : B ≃* DihedralGroup n)
    (P : Sylow 2 ↥(A ⊔ B)) :
    normalizer (P : Set ↥(A ⊔ B)) = P := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  exact self_normalizing_of_surjective e.toMonoidHom e.surjective
    (self_normalizing_prod (self_normalizing_dihedral n hn eA)
      (self_normalizing_dihedral n hn eB)) P

/-- A two-group kernel does not enlarge the lifted Sylow normalizer. -/
theorem self_normalizing_of_two_kernel {K : Type*} [Group K] [Finite K]
    (f : G →* K) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hK : ∀ P : Sylow 2 K, normalizer (P : Set K) = P)
    (P : Sylow 2 G) : normalizer (P : Set G) = P := by
  have hkp : f.ker ≤ P := hk.le_sylow_of_normal P
  apply le_antisymm _ P.le_normalizer
  have hh := (P : Subgroup G).le_normalizer_map f
  change (normalizer (P : Set G)).map f ≤ normalizer (P.mapSurjective hf : Set K) at hh
  rw [hK (P.mapSurjective hf)] at hh
  change (normalizer (P : Set G)).map f ≤ (P : Subgroup G).map f at hh
  have hh' := map_le_iff_le_comap.mp hh
  rwa [comap_map_eq_self hkp] at hh'

end Sylow

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An index-two intersection has no additional normalizer when its Sylow
normalizer inside the index-two subgroup is trivial modulo itself. -/
theorem normalizer_sylow_intersection_eq_of_index_two
    (T : Sylow 2 G) (D : Subgroup G) (hi : D.index = 2)
    (hout : ∃ t ∈ (T : Subgroup G), t ∉ D)
    (hD : ∀ P : Sylow 2 D, normalizer (P : Set D) = P) :
    normalizer ((T : Subgroup G) ⊓ D : Set G) = (T : Subgroup G) := by
  let : D.Normal := normal_of_index_eq_two hi
  let S := (T : Subgroup G) ⊓ D
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (le_inf T.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal D
  have hDN : D ⊓ normalizer (S : Set G) ≤ (T : Subgroup G) := by
    intro x hx
    have hn : (⟨x,hx.1⟩ : D) ∈ normalizer (P : Set D) := by
      rw [show (P : Set D) = ((T : Subgroup G).subgroupOf D : Set D) from congrArg SetLike.coe hP]
      have he : S.subgroupOf D = (T : Subgroup G).subgroupOf D := by
        ext y
        exact and_iff_left y.property
      rw [← he, ← subgroupOf_normalizer_eq (show S ≤ D from inf_le_right)]
      exact hx.2
    rw [hD P] at hn
    change (⟨x,hx.1⟩ : D) ∈ (P : Subgroup D) at hn
    rw [hP] at hn
    exact hn
  apply le_antisymm _ hTS
  intro g hg
  by_cases hgd : g ∈ D
  · exact hDN ⟨hgd,hg⟩
  obtain ⟨t,ht,htD⟩ := hout
  have htdg : t⁻¹*g ∈ D := (D.mul_mem_iff_of_index_two hi).mpr
    (by simp only [inv_mem_iff,htD,hgd])
  have htgn : t⁻¹*g ∈ normalizer (S : Set G) :=
    (normalizer (S : Set G)).mul_mem ((normalizer (S : Set G)).inv_mem (hTS ht)) hg
  have htgt : t⁻¹*g ∈ (T : Subgroup G) := hDN ⟨htdg,htgn⟩
  simpa only [mul_inv_cancel_left] using (T : Subgroup G).mul_mem ht htgt
end Subgroup

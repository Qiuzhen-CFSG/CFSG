module
public import Theory.Quasithin.CoprimeRank

/-!
# Cubic normalizer rank through a binary kernel

When a subgroup contains the kernel of a surjection, its full normalizer
maps onto the normalizer of its image. A two-group kernel preserves cubic
rank on this restricted surjection. The actual noncontained 13.7.19 source
application uses this to lift the two cubic directions in ΓL₂(4).
-/

public noncomputable section
open Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem primeRank_three_normalizer_eq_of_twoGroup_kernel
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (R : Subgroup G) (hR : f.ker ≤ R) :
    primeRank 3 (normalizer (R : Set G)) = primeRank 3 (normalizer (R.map f : Set H)) := by
  have hrange : (R.map f) ≤ f.range := map_le_range f R
  have hc : (R.map f).comap f = R := by
    rw [comap_map_eq, sup_eq_left.mpr hR]
  have hn : (normalizer (R.map f : Set H)).comap f = normalizer (R : Set G) := by
    rw [comap_normalizer_eq_of_le_range hrange, hc]
  have hnmap : (normalizer (R : Set G)).map f = normalizer (R.map f : Set H) := by
    rw [←hn, map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ hf]
    exact le_top
  let N := normalizer (R : Set G)
  have hkN : IsPGroup 2 (f.subgroupMap N).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨n,hn⟩ := hkN.exists_card_eq
  have he := primeRank_eq_of_surjective_of_coprime 3
    (f.subgroupMap N) (f.subgroupMap_surjective N) (by
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n)
  change primeRank 3 N = primeRank 3 (N.map f) at he
  rw [hnmap] at he
  exact he

module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Sylow intersections for index-two local components

Subnormal restriction makes `R ∩ L` Sylow in `L`; maximality then gives
`S ∩ L = R ∩ L` when `R ≤ S`. Intersecting with any subgroup cannot
increase the index `|S:R|`. All subnormality and indices below are relative
to the stated overgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
proof of Lemma 1.2.5, printed p.505 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.IndexTwo
variable {G : Type*} [Group G] [Finite G]

/-- Homomorphisms preserve relative Sylow membership in their images. -/
theorem isSylowIn_map {S H : Subgroup G} (hS : IsSylowIn 2 S H)
    {X : Type*} [Group X] (f : G →* X) :
    IsSylowIn 2 (S.map f) (H.map f) := by
  obtain ⟨T, hT⟩ := hS
  refine ⟨T.mapSurjective (f := f.subgroupMap H) (f.subgroupMap_surjective H), ?_⟩
  change ((T : Subgroup H).map (f.subgroupMap H)).map (H.map f).subtype = S.map f
  rw [map_map]
  change (T : Subgroup H).map (f.comp H.subtype) = _
  rw [← map_map, hT]

/-- Taking images cannot increase a finite relative index. -/
theorem map_relIndex_le {X : Type*} [Group X] (f : G →* X) (A B : Subgroup G) :
    (A.map f).relIndex (B.map f) ≤ A.relIndex B := by
  rw [← relIndex_comap, comap_map_eq]
  exact relIndex_le_of_le_left le_sup_left (A.subgroupOf B).index_ne_zero_of_finite

/-- Sylow restriction to a relatively subnormal subgroup. -/
theorem isSylowIn_inf_of_subnormal {S H K : Subgroup G}
    (hS : IsSylowIn 2 S H) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsSubnormal) :
    IsSylowIn 2 (S ⊓ K) K := by
  obtain ⟨T, hT⟩ := hS
  obtain ⟨U, hU⟩ := T.exists_subgroupOf_eq_of_subnormal (K.subgroupOf H) hK
  let e := subgroupOfEquivOfLe hKH
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((U : Subgroup (K.subgroupOf H)).map e.toMonoidHom).map K.subtype = _
  rw [hU, map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hT ▸ mem_map.mpr ⟨y.1, hy, rfl⟩, y.2⟩
  · rintro ⟨hxS, hxK⟩
    obtain ⟨t, ht, he⟩ := mem_map.mp (hT.symm ▸ hxS)
    change (t : G) = x at he
    have htK : (t : G) ∈ K := he.symm ▸ hxK
    exact ⟨⟨t, htK⟩, ht, he⟩

/-- The two local Sylow intersections in the proof of Lemma 1.2.5 coincide. -/
theorem local_component_sylow_intersection (S : Sylow 2 G)
    {L R : Subgroup G} (hRS : R ≤ S) (hL : L ∈ Chapter1.L G R) :
    IsSylowIn 2 (R ⊓ L) L ∧ (S : Subgroup G) ⊓ L = R ⊓ L := by
  have hSyl := isSylowIn_inf_of_subnormal hL.2.1 le_sup_left hL.1.subnormal
  refine ⟨hSyl, ?_⟩
  obtain ⟨_, _, hm⟩ := isSylowIn_iff.mp hSyl
  exact hm _ (S.isPGroup'.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left))
    (inf_le_inf_right L hRS) inf_le_right

omit [Finite G] in
/-- The source's index bound remains valid after intersection. -/
theorem intersection_relIndex_le_two {S R : Subgroup G}
    (hidx : R.relIndex S = 2) (P : Subgroup G) :
    (R ⊓ P).relIndex (S ⊓ P) ≤ 2 := by
  have he : (R ⊓ P).relIndex (S ⊓ P) = R.relIndex (S ⊓ P) := by
    rw [← inf_relIndex_right, inf_assoc, inf_left_comm P S, inf_idem,
      inf_relIndex_right]
  rw [he]
  exact hidx ▸ relIndex_le_of_le_right inf_le_left (hidx ▸ by decide)

end CFSG.Quasithin.Chapter1.Section02.IndexTwo

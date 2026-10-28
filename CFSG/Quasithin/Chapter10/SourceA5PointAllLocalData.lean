module

public import CFSG.Quasithin.Chapter10.SourceA5PointCarrierData

/-!
# Local data for every original point with a stabilizing Sylow

Restrict the prescribed full point-centralizer Sylow to the containing
C-component, then map it through the literal central quotient. The original
local component and moved elementary subgroup retain their normalization,
local membership and cardinal bounds. These proofs need only that the
point Sylow normalizes L; they impose no condition on whether the point
centralizes the full local orbit.

The all-point stabilization theorem supplies this premise for every escaping
original point. These interfaces feed the all-point quasisimple inspection
in Aschbacher–Smith 10.2.9, printed pp.750–751, including the fixed-point
branch. They preserve the original Sylow, containing component and quotient
maps of SourceA5PointLocalEmbedding and SourceA5PointCarrierData.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Restrict the prescribed full point-centralizer Sylow to the same component. -/
theorem source_point_containing_component_local_sylow_of_normalizes
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    ∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype =
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I ∧
      (S : Subgroup I) ≤ normalizer (L.subgroupOf I : Set I) ∧
      L.subgroupOf I ∈ localCComponents S := by
  let R := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  obtain ⟨S,hSm⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hIX hI.subnormal
  have hSe : (S : Subgroup I) = R.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hSm,subgroupOf_map_subtype]
  have hlocal : L ∈ localCComponents R :=
    localCComponents_antitone inf_le_left D.maximal.1.1
  refine ⟨S,hSm,?_,?_⟩
  · rw [hSe,←subgroupOf_normalizer_eq hLI]
    exact comap_mono hstab
  · rw [hSe]
    exact SourceEmbeddings.local_restrict hlocal hLI

/-- The literal central quotient retains full Sylow-local data and the moved bound. -/
theorem source_a5_point_center_quotient_local_embedding_of_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    ∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype =
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I ∧
      L.subgroupOf I ∈ localCComponents S ∧
      let q := QuotientGroup.mk' (center I)
      let B := (L.subgroupOf I).map q
      let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
      B ∈ localCComponents Sbar ∧
      (Sbar : Subgroup (I ⧸ center I)) ≤ normalizer (B : Set _) ∧
      B ≠ ⊤ ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
      16 ≤ Nat.card (center (pCore 2 B)) := by
  obtain ⟨S,hSm,hnS,hl⟩ := source_point_containing_component_local_sylow_of_normalizes D hstab hs hLI.le hIX hI
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  refine ⟨S,hSm,hl,?_,?_,?_,⟨source_a5_containing_center_image_quotient e hLI.le⟩,
    source_a5_marked_core_center_card D e hLI.le (MulEquiv.refl _)⟩
  · exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  · exact (map_mono hnS).trans (le_normalizer_map q)
  · intro he
    have hh : (⊤ : Subgroup I) ≤ L.subgroupOf I :=
      perfect_le_of_map_le_of_central_kernel q (by rw [QuotientGroup.ker_mk'])
        ⊤ (L.subgroupOf I) (by rw [he]; exact le_top)
    exact hLI.ne (le_antisymm hLI.le (subgroupOf_eq_top.mp (top_unique hh)))

/-- The actual full point Sylow normalizes the same original moved image. -/
theorem source_a5_point_center_moved_normalized_of_normalizes
    {v : G} (hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G))
    {I : Subgroup G} (hLI : L ≤ I) (S : Sylow 2 I)
    (hSm : (S : Subgroup I).map I.subtype =
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I) :
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) : Subgroup (I ⧸ center I)) ≤
      normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map
        (QuotientGroup.mk' (center I)) : Set (I ⧸ center I)) := by
  have hRW : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hstab hg),
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T hg.1))]
  have hSW : (S : Subgroup I) ≤ normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans hLI)]
    intro s hs
    apply hRW
    have hh : (s : G) ∈ (S : Subgroup I).map I.subtype := mem_map_of_mem I.subtype hs
    rw [hSm] at hh
    exact hh.1
  exact (map_mono hSW).trans (le_normalizer_map (QuotientGroup.mk' (center I)))

end CFSG.Quasithin.Chapter10

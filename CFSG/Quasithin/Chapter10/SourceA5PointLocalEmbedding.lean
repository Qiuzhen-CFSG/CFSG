module
public import CFSG.Quasithin.Chapter10.SourceA5PointCoreCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion
public import CFSG.Quasithin.Chapter10.SourceA5PointRudvalis
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Local data for the original quasisimple point inspection

Restrict the original full point-centralizer Sylow to the same containing
C-component I. The restriction still normalizes the original L and retains
its local C-component membership. Mapping this exact Sylow through I/Z(I)
preserves local membership and normalization; perfection keeps the smaller
image proper. Its A₅ quotient and the lower bound sixteen on its core center
are transported through the literal quotient map.

The original moved seed also retains its full normalizer control inside I.
The Rudvalis consumer below removes its separate Sylow-local premise using
these source data. Selection of the marked A.3.12/A.3.14 embedding row remains
a separate theorem; a carrier label is not used as an embedding hypothesis.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, and A.3.12/A.3.14.
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
theorem source_point_containing_component_local_sylow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
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
  have hRL : R ≤ normalizer (L : Set G) :=
    (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0)
  obtain ⟨S,hSm⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hIX hI.subnormal
  have hSe : (S : Subgroup I) = R.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hSm,subgroupOf_map_subtype]
  have hlocal : L ∈ localCComponents R :=
    localCComponents_antitone inf_le_left D.maximal.1.1
  refine ⟨S,hSm,?_,?_⟩
  · rw [hSe,←subgroupOf_normalizer_eq hLI]
    exact comap_mono hRL
  · rw [hSe]
    exact SourceEmbeddings.local_restrict hlocal hLI

/-- The original moved seed has its full normalizer controlled by L. -/
theorem source_a5_original_seed_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
  (le_inf (source_a5_moved_normalizer_le D e ht htn hcross) le_rfl).trans
    (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross)

/-- The same seed-normalizer control holds inside the actual containing component. -/
theorem source_a5_containing_seed_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {I : Subgroup G} (hLI : L ≤ I) :
    normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) ≤
      normalizer (L.subgroupOf I : Set I) := by
  rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans hLI),
    ←subgroupOf_normalizer_eq hLI]
  exact comap_mono (source_a5_original_seed_normalizer_le D e ht htn hcross)

/-- The literal central quotient retains full Sylow-local data and the moved bound. -/
theorem source_a5_point_center_quotient_local_embedding
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
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
  obtain ⟨S,hSm,hnS,hl⟩ := source_point_containing_component_local_sylow D hn hvL hv0 hs hLI.le hIX hI
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

/-- The original point geometry discharges the local-membership input of the Ru exclusion. -/
theorem source_a5_point_not_rudvalis
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (eI : (I ⧸ center I) ≃* Rudvalis.Model)
    (hcore : Nat.card (pCore 2
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 2048) : False := by
  obtain ⟨S,_,_,hl⟩ := source_point_containing_component_local_sylow D hn hvL hv0 hs hLI hIX hI
  exact source_a5_not_rudvalis_containing_quotient D e hLI S hl eI hcore

end CFSG.Quasithin.Chapter10


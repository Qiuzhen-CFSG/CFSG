module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.LocalReductions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Quotients
public import Stellmacher.BaumannNormalizer

/-!
# Lifting the source Baumann normalizer through a two-kernel

The preimage of Baum(R)'s image is Baum(R) ker(q). If the kernel lies
in R, Baumann heredity identifies its Baumann subgroup with Baum(R).
Consequently normalizing the quotient image lifts to normalizing the
original Baumann subgroup. The source application uses the literal plus
map and 13.6.5; it does not identify a quotient normalizer with an ambient
one while discarding the kernel.

Source: Aschbacher–Smith, combined manuscript, B.2.3(4), printed p.75,
and the Frattini step in 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection
variable {G D : Type*} [Group G] [Group D] [Finite G]

/-- Baumann heredity accounts for the entire quotient kernel. -/
theorem baumann_normalizer_comap (q : G →* D) (R : Subgroup G) (hk : q.ker ≤ R) :
    (normalizer ((ChapterB.baumann R).map q : Set D)).comap q =
      normalizer (ChapterB.baumann R : Set G) := by
  have he : ChapterB.baumann ((ChapterB.baumann R).map q |>.comap q) =
      ChapterB.baumann R := by
    apply (ChapterB.lemma_B_2_3_4 R _ (le_comap_map _ _) ?_).symm
    rw [comap_map_eq]
    exact sup_le inf_le_left hk
  apply le_antisymm
  · have hn : normalizer (((ChapterB.baumann R).map q).comap q : Set G) ≤
        normalizer (ChapterB.baumann (((ChapterB.baumann R).map q).comap q) : Set G) :=
      normalizer_le_normalizer_baumann _
    rw [he] at hn
    exact (((ChapterB.baumann R).map q).le_normalizer_comap q).trans hn
  · intro x hx
    exact (ChapterB.baumann R).le_normalizer_map q (mem_map_of_mem q hx)

/-- The normal kernel lies in every Sylow subgroup when it is a two-group. -/
theorem baumann_normalizer_comap_of_two_kernel (q : G →* D) (R : Sylow 2 G)
    (hk : IsPGroup 2 q.ker) :
    (normalizer ((ChapterB.baumann (R : Subgroup G)).map q : Set D)).comap q =
      normalizer (ChapterB.baumann (R : Subgroup G) : Set G) :=
  baumann_normalizer_comap q R (hk.le_sylow_of_normal R)

omit [Finite G] in
/-- Transport an internal Baumann subgroup to its literal ambient image. -/
theorem baumann_subgroupOf_map (H R : Subgroup G) (hR : R ≤ H) :
    (ChapterB.baumann (R.subgroupOf H)).map H.subtype = ChapterB.baumann R := by
  simpa only [ChapterB.baumann, ChapterB.thompsonAlpha, map_subgroupOf_eq_of_le hR] using
    baumann_map_injective H.subtype H.subtype_injective (R.subgroupOf H)

/-- Exact inverse image of the Baumann normalizer under the literal plus map. -/
theorem source_plus_baumann_normalizer_comap
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v)) :
    (normalizer (plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) : Set _)).comap
      (plusMk K L T z v hL hz) =
        (normalizer (ChapterB.baumann (Tv T v) : Set G)).subgroupOf (plusActor K L T v) := by
  let H := plusActor K L T v
  let R := (Tv T v).subgroupOf H
  have hRH : Tv T v ≤ H := le_sup_right
  have hB := baumann_subgroupOf_map H (Tv T v) hRH
  have hi : (ChapterB.baumann (Tv T v)).subgroupOf H = ChapterB.baumann R := by
    rw [← hB]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [plusImage, hi, baumann_normalizer_comap _ R hk, ← hi]
  exact (subgroupOf_normalizer_eq
    (show ChapterB.baumann (Tv T v) ≤ H from inf_le_left.trans hRH)).symm

/-- The plus-image normalizer lifts inside Gᵥ to Mᵥ by the actual 13.6.5.
The kernel hypothesis can be supplied by its two-group property and the
source Sylow witness using `baumann_normalizer_comap_of_two_kernel`. -/
theorem source_plus_baumann_normalizer_le
    (K L T M : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hk : (plusMk K L T z v hL hz).ker ≤ (Tv T v).subgroupOf (plusActor K L T v))
    (hc : Gv v ⊓ normalizer (ChapterB.baumann (Tv T v) : Set G) ≤ Mv M v) :
    ((normalizer (plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) : Set _)).comap
      (plusMk K L T z v hL hz)).map (plusActor K L T v).subtype ≤ Mv M v := by
  let H := plusActor K L T v
  let R := (Tv T v).subgroupOf H
  have hRH : Tv T v ≤ H := le_sup_right
  have hB := baumann_subgroupOf_map H (Tv T v) hRH
  have hi : (ChapterB.baumann (Tv T v)).subgroupOf H = ChapterB.baumann R := by
    rw [← hB]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  change ((normalizer (((ChapterB.baumann (Tv T v)).subgroupOf H).map
    (plusMk K L T z v hL hz) : Set _)).comap (plusMk K L T z v hL hz)).map H.subtype ≤ _
  rw [hi, baumann_normalizer_comap _ R hk]
  rintro x ⟨y, hy, rfl⟩
  apply hc
  refine ⟨plusActor_le_Gv K L T v hK y.property, ?_⟩
  rw [← hB]
  exact (ChapterB.baumann R).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hy)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix

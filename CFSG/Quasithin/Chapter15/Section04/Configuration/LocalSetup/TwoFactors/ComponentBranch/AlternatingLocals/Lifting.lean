module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Containment
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.Recognition
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# The centralizer index and even local subgroups

The quotient is faithful on the normal component. Hence its kernel is
exactly C_I(L), and the order-two residual centralizer in S₆ lifts into
T_I. This proves [C_{T_I}(Y_i):C_{T_I}(L)] = 2. Intersecting each local
group with L gives an actual S₄ subgroup; no central extension is split
by this calculation alone.

The explicit quotient coordinates remain an upstream construction obligation.
Source: Aschbacher–Smith 15.4.18, combined manuscript, printed p.1163.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
variable {I : Type*} [Group I] {L : Subgroup I} (d : QuotientCoordinates L)
include d

theorem component_centralizer_eq_kernel :
    centralizer (L : Set I) = d.quotientMap.ker := by
  rw [← d.centralizer_lift L le_rfl,
    show L.map d.quotientMap = A6 from d.component_image,
    ResidualPairRecognition.ComponentLocals.centralizer_alternating, MonoidHom.comap_bot]

variable [Finite I]

theorem sylow_component_centralizer (T : Sylow 2 I) :
    (T : Subgroup I) ⊓ centralizer (L : Set I) = d.quotientMap.ker := by
  rw [d.component_centralizer_eq_kernel, inf_eq_right.mpr (d.kernel_le_sylow T)]

/-- The image of each local group is an actual S₆ parabolic, with all
centralizer and even-subgroup assertions in these same coordinates. -/
theorem parabolic_image_structure (T : Sylow 2 I) (Y : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3) :
    Nat.card (centralizer (Y.map d.quotientMap : Set S6)) = 2 ∧
      centralizer (Y.map d.quotientMap : Set S6) ≤ (T : Subgroup I).map d.quotientMap ∧
      centralizer (Y.map d.quotientMap : Set S6) ≤
        centralizer ((Y ⊔ (T : Subgroup I)).map d.quotientMap : Set S6) ∧
      Disjoint (centralizer (Y.map d.quotientMap : Set S6)) A6 ∧
      Nonempty (↥((Y ⊔ (T : Subgroup I)).map d.quotientMap ⊓ A6) ≃*
        Equiv.Perm (Fin 4)) ∧
      centralizer (Y.map d.quotientMap : Set S6) ⊔
        ((Y ⊔ (T : Subgroup I)).map d.quotientMap ⊓ A6) =
        (Y ⊔ (T : Subgroup I)).map d.quotientMap := by
  let P := T.mapSurjective d.quotientMap_surjective
  let H := (Y ⊔ (T : Subgroup I)).map d.quotientMap
  have hp : (P : Subgroup S6) ≤ H := map_mono le_sup_right
  have hi' : (P : Subgroup S6).relIndex H = 3 := by
    change ((T : Subgroup I).map d.quotientMap).relIndex H = 3
    rw [relIndex_map_map, sup_of_le_left (d.kernel_le_sylow T),
      sup_of_le_left ((d.kernel_le_sylow T).trans le_sup_right)]
    exact hi
  have hr : (pResidual 2 H).map H.subtype = Y.map d.quotientMap := by
    rw [← map_embedded_pResidual, embedded_pResidual_join_pGroup Y (T : Subgroup I)
      hY T.isPGroup' hn]
  obtain ⟨hc, hct, hch, hd, he, _⟩ :=
    ResidualPairRecognition.ComponentLocals.local_structure P H hp hi'
  have hs := ResidualPairRecognition.ComponentLocals.local_product P H hp hi'
  dsimp only at hc hct hch hd he hs
  rw [hr] at hc hct hch hd hs
  exact ⟨hc, hct, hch, hd, he, hs⟩

/-- The entire order-two model centralizer lifts into the specified Sylow
subgroup, and centralization lifts by faithfulness on the component. -/
theorem map_sylow_factor_centralizer (T : Sylow 2 I) (Y : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3) :
    ((T : Subgroup I) ⊓ centralizer (Y : Set I)).map d.quotientMap =
      centralizer (Y.map d.quotientMap : Set S6) := by
  apply le_antisymm
  · exact (map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _)
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := (d.parabolic_image_structure T Y hY hn hi).2.1 hz
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    rw [← d.centralizer_lift Y (d.factor_le_component Y hY)]
    exact hz

/-- The index required by the index-two invariance argument, proved from
compatible quotient coordinates and the local factor hypotheses. -/
theorem factor_centralizer_index (T : Sylow 2 I) (Y : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3) :
    ((T : Subgroup I) ⊓ centralizer (L : Set I)).relIndex
      ((T : Subgroup I) ⊓ centralizer (Y : Set I)) = 2 := by
  rw [d.sylow_component_centralizer T, ← MonoidHom.comap_bot,
    relIndex_comap, relIndex_bot_left, d.map_sylow_factor_centralizer T Y hY hn hi]
  exact (d.parabolic_image_structure T Y hY hn hi).1

omit [Finite I] in
/-- Mapping an intersection with the component preserves the intersection
when the other subgroup contains the quotient kernel. -/
theorem map_inf_component (H : Subgroup I) (hkH : d.quotientMap.ker ≤ H) :
    (H ⊓ L).map d.quotientMap = H.map d.quotientMap ⊓ A6 := by
  let q := d.quotientMap
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left) ((map_mono inf_le_right).trans_eq d.component_image)
  · rintro z ⟨hzH, hzA⟩
    obtain ⟨l, hl, rfl⟩ := (show z ∈ L.map q from d.component_image.symm ▸ hzA)
    have hlH : l ∈ H := by
      have hpre : l ∈ (H.map q).comap q := hzH
      rwa [comap_map_eq, sup_of_le_left hkH] at hpre
    exact ⟨l, ⟨hlH, hl⟩, rfl⟩

/-- The even local subgroup maps isomorphically onto the S₄ parabolic
inside A₆. The kernel lies in the local Sylow subgroup. -/
theorem even_local_equiv (T : Sylow 2 I) (Y : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3) :
    Nonempty (↥((Y ⊔ (T : Subgroup I)) ⊓ L) ≃* Equiv.Perm (Fin 4)) := by
  let H := Y ⊔ (T : Subgroup I)
  let q := d.quotientMap
  have hm := d.map_inf_component H ((d.kernel_le_sylow T).trans le_sup_right)
  let e : (H ⊓ L : Subgroup I) ≃* (H ⊓ L).map q :=
    MulEquiv.ofBijective (q.subgroupMap (H ⊓ L))
      ⟨fun _ _ he => d.factor_map_injective inf_le_right (congrArg Subtype.val he),
        q.subgroupMap_surjective _⟩
  exact (d.parabolic_image_structure T Y hY hn hi).2.2.2.2.1.map
    fun j => e.trans ((MulEquiv.subgroupCongr hm).trans j)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates

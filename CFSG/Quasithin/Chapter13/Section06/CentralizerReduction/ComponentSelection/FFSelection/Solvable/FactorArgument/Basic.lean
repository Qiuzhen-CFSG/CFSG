module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Configuration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Quotients
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual actors in the solvable factor argument

The subgroup L_v is an embedded two-residual. Its literal star image is
therefore two-perfect, and the earlier cubic quotient L_v/O₂(L_v) bounds
its order by three times a power of two. The given Sylow witness maps to
the literal T_v star image and preserves the L_v star image.

The marked seed moves U_H already from U_X ≤ U_H; this particular inference
does not require the separate irreducibility argument. These are inputs to
factor identification, not an assertion of that identification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
variable {G : Type*} [Group G]
namespace FactorArgument

/-- The literal quotient image of L_v remains two-perfect. -/
theorem starLv_twoPerfect [Finite G] (L : Subgroup G) (z v : G) :
    IsPPerfect 2 (starImage z v (Lv L v)) :=
  (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)).of_surjective
    (starImageMap z v (Lv L v) (Lv_le_Gv L v))
    (starImageMap_surjective z v (Lv L v) (Lv_le_Gv L v))

/-- The earlier quotient of order three bounds the actual star image. -/
theorem starLv_card_dvd [Finite G] (L : Subgroup G) (z v : G)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    ∃ n : ℕ, Nat.card (starImage z v (Lv L v)) ∣ 3 * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Lv L v)).exists_card_eq
  have hsize : Nat.card (Lv L v) = 3 * 2 ^ n := by
    rw [← (pCore 2 (Lv L v)).index_mul_card, index_eq_card, hcard, hn]
  refine ⟨n, ?_⟩
  rw [← hsize]
  exact card_dvd_of_surjective (starImageMap z v (Lv L v) (Lv_le_Gv L v))
    (starImageMap_surjective z v (Lv L v) (Lv_le_Gv L v))

/-- Normalization survives restriction to G_v and the actual quotient map. -/
theorem starTv_normalizes_starLv (L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G)) :
    starImage z v (Tv T v) ≤ normalizer (starImage z v (Lv L v) : Set _) := by
  have hn : (Tv T v).subgroupOf (Gv v) ≤
      normalizer ((Lv L v).subgroupOf (Gv v) : Set (Gv v)) := by
    rw [← subgroupOf_normalizer_eq (Lv_le_Gv L v)]
    exact comap_mono hL
  exact (map_mono hn).trans (le_normalizer_map _)

/-- The supplied Sylow maps onto precisely T_v*, not an auxiliary actor. -/
theorem exists_starSylow [Finite G] (T : Subgroup G) (z v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v) :
    ∃ P : Sylow 2 (Gstar z v), (P : Subgroup (Gstar z v)) = starImage z v (Tv T v) := by
  refine ⟨S.mapSurjective (starMk_surjective z v), ?_⟩
  have he : (S : Subgroup (Gv v)) = (Tv T v).subgroupOf (Gv v) := by
    rw [← hS]
    exact (comap_map_eq_self_of_injective (Gv v).subtype_injective _).symm
  rw [Sylow.coe_mapSurjective, he]
  rfl

end FactorArgument

/-- The nonzero marked commutator propagates to U_H by containment alone. -/
theorem NormalS3Decomposition.marked_UH_commutator_ne_bot [Finite G]
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) :
    ⁅movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H,
      Lv L (A5Module.markedV s)⁆ ≠ ⊥ := by
  have hne := (marked_Xz_commutators_ne_bot s T S hS hfix
    (XFamily_subset_Xz L T _ _ hX)).2
  intro hzero
  apply hne
  exact le_bot_iff.mp ((commutator_mono (d.UX_le L _ _) le_rfl).trans hzero.le)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end

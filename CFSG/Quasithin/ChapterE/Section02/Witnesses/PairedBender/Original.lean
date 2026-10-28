module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.AllModels
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.MarkedLift
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

/-!
# Full original paired E.2.7–9 source construction

The original C-component becomes a simple ordinary component in H/J.
Its failure of normality is preserved, and Theorem A supplies SQTK for
this actual quotient. The original elementary V has a nontrivial image,
normal in the prescribed quotient Sylow and contained in the image maximal
two-core. The complete paired dispatcher constructs its model and witness.
The genuine marked pair lift then restores all of the original V and the
original maximal subgroup, preserving the quotient model and degree divisor.

Only the genuine earlier Theorems A and C remain explicit. No component
model or witness conclusion is assumed. Source: Aschbacher–Smith E.2.7–9,
printed pp.218–222.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- Construct the full paired witness on the original group and subgroup V. -/
theorem original_source
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP) :
    ∃ n : ℕ, ModelAt (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) n ∧
      Nonempty (BenderPlacement.OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  have hDn : ¬ D.Normal := fun hd => hn (cComponent_normal_of_quotient_normal hK J hd)
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  have hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
  let hPs := ChapterB.minimalParabolic_surjective_core T hP q (QuotientGroup.mk'_surjective J) hk
  have hJs : ChapterB.minimalParabolicCore S hPs = ⊥ :=
    (Structure.source_star_minimal_core_free T hP).2
  have hM : ChapterB.minimalParabolicMax S hPs = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J) hk).symm
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hPs).pCoreIn 2 := by
    rw [hM]
    exact (map_mono hVM).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  obtain ⟨n,hm,⟨w⟩⟩ := coreFree_source hC (Structure.source_star_sqtk hA hH T hP hs)
    S hPs hsX hJs D hi.2.1 hi.2.2.2 hDn W hWS hSW hWcore hne
  rw [hM] at w
  exact ⟨n,hm,BenderPlacement.lift_original_witness T hP V hVT hvn hVM w⟩

end CFSG.Quasithin.ChapterE.Witnesses.PairedBender

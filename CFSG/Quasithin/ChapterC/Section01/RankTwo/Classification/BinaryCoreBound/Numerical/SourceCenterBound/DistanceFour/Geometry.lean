module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.FullSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition

/-!
# Center of the actual binary core at distance four

The source span recognition and full-span generation give
V_alpha = B_alpha join core_alpha. Since B_alpha is the center of V_alpha,
the center of the core is exactly its intersection with Z_alpha. This is
the center identification required by the numerical Chapter C consumer.

Source: Meierfrankenfeld--Stellmacher (1993), the b=4 argument (4.6),
especially the starred-span generation in (4.6.12), pp.910--912.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour

open MS93 MS93.DistanceFour

private theorem centralizer_join {G : Type*} [Group G] (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left)
      (le_centralizer_iff.mp inf_le_right)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
  (hb : geometry.b R = 4)

include common radius hb in
theorem radius_generation :
    V R (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) ⊔ core R (alpha R) := by
  have hs := (LargeBranch.fullSpans source common radius hb
    (LargeBranch.RankOne.source_spanRecognition common radius hb)).2
  have hZB := Flags.Z_le_B geometry (alpha R)
    (geometry.V_local (alpha R) rfl common.large_distance)
  rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts
    common.large_distance (alpha R) (beta R) rfl (base_adjacent R), hs]
  rw [← sup_assoc, sup_eq_left.mpr hZB]

include common radius hb in
/-- The center is identified by generation of the actual radius group.
The equality allows a nonzero fixed kernel modulo U. -/
theorem center_core_image :
    (center (core R (alpha R))).map (core R (alpha R)).subtype =
      core R (alpha R) ⊓ Z R (alpha R) := by
  let C := core R (alpha R)
  let A := V R (alpha R)
  let B₀ := B R (alpha R) (geometry.Z_normal (alpha R))
  have hCA : C ≤ A := radius.core_le_radius (alpha R) rfl
  have hBA : B₀ = (center A).map A.subtype := radius.B_eq_center (alpha R) rfl
  have hZB : Z R (alpha R) ≤ B₀ := Flags.Z_le_B geometry (alpha R)
    (geometry.V_local (alpha R) rfl common.large_distance)
  have hgen : A = B₀ ⊔ C := radius_generation source common radius hb
  apply le_antisymm
  · rintro x ⟨c, hc, rfl⟩
    have hC : (c : FreeAmalgam R) ∈ centralizer (C : Set (FreeAmalgam R)) := by
      intro y hy
      exact congrArg C.subtype ((mem_center_iff.mp hc) ⟨y, hy⟩)
    have hB : (c : FreeAmalgam R) ∈ centralizer (B₀ : Set (FreeAmalgam R)) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hBA.le hy
      exact (congrArg A.subtype ((mem_center_iff.mp hz) ⟨c, hCA c.property⟩)).symm
    have hA : (c : FreeAmalgam R) ∈ centralizer (A : Set (FreeAmalgam R)) := by
      rw [hgen, centralizer_join]
      exact ⟨hB, hC⟩
    have hcB : (c : FreeAmalgam R) ∈ B₀ := by
      rw [hBA]
      refine ⟨⟨c, hCA c.property⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hA y y.property)
    exact ⟨c.property, SmallBranch.core_inter_B_le_Z source geometry common radius
      (alpha R) (beta R) rfl (base_adjacent R) ⟨c.property, hcB⟩⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hBA.le (hZB hx.2)
    refine ⟨⟨z, hx.1⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg A.subtype ((mem_center_iff.mp hz) ⟨y, hCA y.property⟩))

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceFour

module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections.Model
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
public import Theory.GroupTheory.WeakClosureNormalizer

/-!
# Literal marked intersections for the Mathieu coset geometry

Transport the model coordinate bijections through the original centralizer
marking to obtain the intersection orders 8, 4, and 16. The centralizer of
each row intersection lies in the normalizer of the corresponding rectangle,
by the model calculation. Its normalizer therefore also preserves the rectangle:
a conjugate rectangle in its normalizer equals it by Sylow weak closure.
Intersecting with the row normalizer gives the literal two parabolic identities
used in the source geometry, without assuming any ambient quotient type.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(3), 39.6(4), and 41.1,
printed pp.213–215 and 219–220.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem pullback_inf (A B : Subgroup SL) :
    F.pullback (A ⊓ B) = F.pullback A ⊓ F.pullback B := by
  ext x
  constructor
  · intro hx
    have hc := F.pullback_le (A ⊓ B) hx
    have hm := (F.mem_pullback_iff (A ⊓ B) ⟨x, hc⟩).mp hx
    exact ⟨(F.mem_pullback_iff A ⟨x, hc⟩).mpr hm.1,
      (F.mem_pullback_iff B ⟨x, hc⟩).mpr hm.2⟩
  · rintro ⟨ha, hb⟩
    have hc := F.pullback_le A ha
    exact (F.mem_pullback_iff (A ⊓ B) ⟨x, hc⟩).mpr
      ⟨(F.mem_pullback_iff A ⟨x, hc⟩).mp ha,
        (F.mem_pullback_iff B ⟨x, hc⟩).mp hb⟩

private def intersectionEquiv (A B : Subgroup SL) (hA : A ≤ centralizer) :
    ↥(F.pullback A ⊓ F.pullback B) ≃* ↥(A ⊓ B) :=
  (MulEquiv.subgroupCongr (pullback_inf F A B).symm).trans
    (F.pullbackEquiv (A ⊓ B) (inf_le_left.trans hA))

/-- The marked row-plane intersection has order eight in the original group. -/
theorem row_plane_card : Nat.card ↥(F.row ⊓ F.plane) = 8 := by
  rw [Nat.card_congr (intersectionEquiv F Model.row Model.plane Model.row_le_centralizer).toEquiv,
    Nat.card_congr modelRowPlaneCoordinates]
  simp

/-- The marked row-three-space intersection has order four. -/
theorem row_threeSpace_card : Nat.card ↥(F.row ⊓ F.threeSpace) = 4 := by
  rw [Nat.card_congr (intersectionEquiv F Model.row Model.threeSpace Model.row_le_centralizer).toEquiv,
    Nat.card_congr modelRowThreeSpaceCoordinates]
  simp

/-- The two marked rectangles meet in a group of order sixteen. -/
theorem planes_intersection_card : Nat.card ↥(F.plane ⊓ F.threeSpace) = 16 := by
  rw [Nat.card_congr (intersectionEquiv F Model.plane Model.threeSpace Model.plane_le_centralizer).toEquiv,
    Nat.card_congr modelPlanesIntersectionCoordinates]
  simp

private theorem relative_normalizer_intersection (k : ℕ) (hk : k = 2 ∨ k = 3) :
    Subgroup.centralizer ({z} : Set G) ⊓
        normalizer ((F.row ⊓ F.pullback (rectangle k) : Subgroup G) : Set G) ≤
      normalizer (F.pullback (rectangle k) : Set G) := by
  have hI := F.pullback_relativeNormalizer (Model.row ⊓ rectangle k)
    (inf_le_left.trans Model.row_le_centralizer)
  rw [pullback_inf F Model.row (rectangle k)] at hI
  have hA := F.pullback_relativeNormalizer (rectangle k)
    ((rectangle_le_upper k).trans upper_le_centralizer)
  have hm : F.pullback (centralizer ⊓ normalizer ((Model.row ⊓ rectangle k : Subgroup SL) : Set SL)) ≤
      F.pullback (centralizer ⊓ normalizer (rectangle k : Set SL)) :=
    map_mono (map_mono (comap_mono (le_inf inf_le_left
      (model_normalizer_row_intersection k hk))))
  rw [hI, hA] at hm
  exact hm.trans inf_le_right

private theorem centralizer_intersection_le (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hz : z ∈ F.pullback (rectangle k)) :
    Subgroup.centralizer ((F.row ⊓ F.pullback (rectangle k) : Subgroup G) : Set G) ≤
      normalizer (F.pullback (rectangle k) : Set G) := by
  intro c hc
  apply relative_normalizer_intersection F k hk
  exact ⟨mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hc z ⟨point_mem_row F, hz⟩).symm),
    centralizer_le_normalizer _ hc⟩

private theorem normalizer_le_of_weak_closure [Finite G]
    (A D : Subgroup G) (hAS : A ≤ (sourceSylow F : Subgroup G))
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (sourceSylow F : Subgroup G) →
      g ∈ normalizer (A : Set G))
    (hAD : A ≤ Subgroup.centralizer (D : Set G))
    (hDN : Subgroup.centralizer (D : Set G) ≤ normalizer (A : Set G)) :
    normalizer (D : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (sourceSylow F).conjugate_eq_of_le_normalizer_of_weakly_closed A hAS
    (fun a ha => mem_normalizer_iff_map_conj_eq.mp (hweak a ha))
  have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hAD).trans
    (map_centralizer_le_centralizer_image (D : Set G) (MulAut.conj g).toMonoidHom)
  have he : (MulAut.conj g).toMonoidHom '' (D : Set G) = (D : Set G) :=
    mem_normalizer_iff_conj_image_eq.mp hg
  rw [he] at hm
  exact hm.trans hDN

/-- The ambient stabilizer of the marked row-plane intersection preserves
the entire plane, by its source weak closure. -/
theorem row_plane_intersection_normalizer_le [Finite G] (hfusion : F.MathieuFusion) :
    normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G) ≤ planeNormalizer F := by
  apply normalizer_le_of_weak_closure F F.plane (F.row ⊓ F.plane)
    (flag_le_sourceSylow F).2.2.1 (plane_weakly_closed F hfusion)
  · intro a ha
    have hca : a ∈ Subgroup.centralizer (F.plane : Set G) := (plane_centralizer_eq F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun d hd => mem_centralizer_iff.mp hca d hd.2
  · exact centralizer_intersection_le F 2 (Or.inl rfl) (point_mem_plane F)

/-- The analogous ambient normalizer containment at the two-dimensional
parabolic of the row action. -/
theorem row_threeSpace_intersection_normalizer_le [Finite G] (hfusion : F.MathieuFusion) :
    normalizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) ≤ threeSpaceNormalizer F := by
  apply normalizer_le_of_weak_closure F F.threeSpace (F.row ⊓ F.threeSpace)
    (flag_le_sourceSylow F).2.2.2 (threeSpace_weakly_closed F hfusion)
  · intro a ha
    have hca : a ∈ Subgroup.centralizer (F.threeSpace : Set G) :=
      (threeSpace_centralizer_eq F).symm ▸ ha
    exact mem_centralizer_iff.mpr fun d hd => mem_centralizer_iff.mp hca d hd.2
  · exact centralizer_intersection_le F 3 (Or.inr rfl) (point_mem_threeSpace F)

/-- The actual line stabilizer in the source coset geometry preserves exactly
the marked hyperplane of the row module. -/
theorem row_plane_normalizer [Finite G] (hfusion : F.MathieuFusion) :
    rowNormalizer F ⊓ planeNormalizer F =
      rowNormalizer F ⊓ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_left inf_normalizer_le_normalizer_inf
  · exact inf_le_inf_left _ (row_plane_intersection_normalizer_le F hfusion)

/-- The actual plane stabilizer in the source coset geometry preserves exactly
the marked two-space of the row module. -/
theorem row_threeSpace_normalizer [Finite G] (hfusion : F.MathieuFusion) :
    rowNormalizer F ⊓ threeSpaceNormalizer F =
      rowNormalizer F ⊓ normalizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_left inf_normalizer_le_normalizer_inf
  · exact inf_le_inf_left _ (row_threeSpace_intersection_normalizer_le F hfusion)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer

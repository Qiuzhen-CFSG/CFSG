module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.RectangleAgreement
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangles
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersections
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-! The exact displacement subgroup in the rectangle agreement problem.
The centralizer of the common sixteen is the product of the two original
elementary sixty-fours and has order 256. The calculation uses the eight
remaining upper matrix entries in the original centralizer marking.

Innerness of every rectangle-preserving automorphism of the full overlap
is a separate step; this file identifies its possible displacement subgroup.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear

private theorem model_common_centralizer :
    Subgroup.centralizer ((Model.plane ⊓ Model.threeSpace : Subgroup SL) : Set SL) =
      Model.plane ⊔ Model.threeSpace := by
  apply le_antisymm
  · intro g hg
    have hupper := UniquenessMathieu.OctadSource.model_planes_centralizer_le_upper hg
    have hentry := SylowCoordinates.upper_entry ⟨g,hupper⟩
    have hdiag (i : Fin 5) : g i i = 1 := by simpa using hentry i i le_rfl
    have hlower (i j : Fin 5) (h : j < i) : g i j = 0 := by
      simpa only [if_neg (ne_of_gt h)] using hentry i j h.le
    have h13 : root (by decide : (1 : Fin 5) < 3) * g =
        g * root (by decide : (1 : Fin 5) < 3) :=
      mem_centralizer_iff.mp hg _ ⟨subset_closure ⟨1,3,by decide,by decide,by decide,rfl⟩,
        subset_closure ⟨1,3,by decide,by decide,by decide,rfl⟩⟩
    have h03 : root (by decide : (0 : Fin 5) < 3) * g =
        g * root (by decide : (0 : Fin 5) < 3) :=
      mem_centralizer_iff.mp hg _ ⟨subset_closure ⟨0,3,by decide,by decide,by decide,rfl⟩,
        subset_closure ⟨0,3,by decide,by decide,by decide,rfl⟩⟩
    have h01 : g 0 1 = 0 := by
      simpa using root_commuting_column g 1 3 (by decide) h13 0
    have h34 : g 3 4 = 0 := by
      simpa using root_commuting_row g 0 3 (by decide) h03 4
    let a := RectangleCoordinates.word3 ![0,0,0,0,g 2 3,g 2 4]
    let b := RectangleCoordinates.word2 ![g 0 2,g 0 3,g 0 4,g 1 2,g 1 3,g 1 4]
    have he : a*b=g := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul,a,b,
        RectangleCoordinates.word3_val,RectangleCoordinates.word2_val]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.single,Matrix.one_apply,h01,h34]
      all_goals first | exact (hdiag _).symm | exact (hlower _ _ (by decide)).symm
    rw [←he]
    exact (Model.plane ⊔ Model.threeSpace).mul_mem
      (mem_sup_right (RectangleCoordinates.word3_mem _))
      (mem_sup_left (RectangleCoordinates.word2_mem _))
  · apply sup_le
    · let := model_rectangle_commutative 2
      exact Model.plane.le_centralizer.trans (centralizer_le inf_le_left)
    · let := model_rectangle_commutative 3
      exact Model.threeSpace.le_centralizer.trans (centralizer_le inf_le_right)

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The full centralizer of the original common sixteen is exactly the join
of the two original rectangles. -/
theorem common_kernel_centralizer_eq_rectangle_join :
    Subgroup.centralizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) =
      F.plane ⊔ F.threeSpace := by
  rw [← pullback_inf F, ← pullback_centralizer F _
    (inf_le_left.trans Model.plane_le_centralizer)
    (show transvection ∈ Model.plane ⊓ Model.threeSpace from
      ⟨subset_closure ⟨0,4,by decide,by decide,by decide,rfl⟩,
        subset_closure ⟨0,4,by decide,by decide,by decide,rfl⟩⟩),
    model_common_centralizer,
    pullback_sup F _ _ Model.plane_le_centralizer Model.threeSpace_le_centralizer]

/-- The rectangle join is self-centralizing, with its centralizer precisely
the original common sixteen. -/
theorem rectangle_join_centralizer :
    Subgroup.centralizer ((F.plane ⊔ F.threeSpace : Subgroup G) : Set G) =
      F.plane ⊓ F.threeSpace := by
  apply le_antisymm
  · exact le_inf
      ((centralizer_le (show F.plane ≤ F.plane ⊔ F.threeSpace from le_sup_left)).trans_eq
        (source_plane_centralizer F))
      ((centralizer_le (show F.threeSpace ≤ F.plane ⊔ F.threeSpace from le_sup_right)).trans_eq
        (source_threeSpace_centralizer F))
  · apply le_centralizer_iff.mp
    rw [common_kernel_centralizer_eq_rectangle_join]

/-- Its center is the literal intersection of the original rectangles. -/
theorem rectangle_join_center :
    (center (F.plane ⊔ F.threeSpace : Subgroup G)).map
      (F.plane ⊔ F.threeSpace : Subgroup G).subtype = F.plane ⊓ F.threeSpace := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    rw [← rectangle_join_centralizer]
    apply mem_centralizer_iff.mpr
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b,hb⟩)
  · intro a ha
    refine ⟨⟨a,mem_sup_left ha.1⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    have hc : a ∈ Subgroup.centralizer ((F.plane ⊔ F.threeSpace : Subgroup G) : Set G) := by
      rwa [rectangle_join_centralizer]
    exact mem_centralizer_iff.mp hc (b : G) b.property

variable [Finite G]

/-- The displacement subgroup has order 256, from the actual sixty-fours
and their marked common sixteen. -/
theorem rectangle_join_card : Nat.card (F.plane ⊔ F.threeSpace : Subgroup G) = 256 := by
  have hN : F.plane ≤ normalizer (F.threeSpace : Set G) :=
    (flag_le_sourceSylow F).2.2.1.trans (plane_normalizers_contain_sourceSylow F).2
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.threeSpace F.plane hN
  rw [source_plane_card,source_threeSpace_card,inf_comm F.threeSpace F.plane,
    UniquenessMathieu.SourceNormalizer.planes_intersection_card,
    sup_comm F.threeSpace F.plane] at hc
  omega

omit [Finite G] in
/-- The center order distinguishing this overlap from the row overlap. -/
theorem rectangle_join_center_card :
    Nat.card (center (F.plane ⊔ F.threeSpace : Subgroup G)) = 16 := by
  have hc := card_map_of_injective
    (K := center (F.plane ⊔ F.threeSpace : Subgroup G))
    (F.plane ⊔ F.threeSpace : Subgroup G).subtype_injective
  rw [rectangle_join_center,UniquenessMathieu.SourceNormalizer.planes_intersection_card] at hc
  exact hc.symm

omit [Finite G] in
/-- Its normality in the full overlap is literal ambient normalization. -/
theorem rectangle_overlap_normalizes_join :
    sourcePlaneNormalizer F ⊓ sourceThreeSpaceNormalizer F ≤
      normalizer ((F.plane ⊔ F.threeSpace : Subgroup G) : Set G) := by
  rw [← common_kernel_centralizer_eq_rectangle_join]
  exact (inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_centralizer (F.plane ⊓ F.threeSpace))

variable {G' : Type*} [Group G'] {z' : G'} (F' : MarkedCentralizer z')

omit [Finite G] in
/-- The two whole comparisons differ inside the exact order-256 rectangle
join; no whole-overlap agreement is assumed. -/
theorem rectangle_maps_displacement_in_join
    (r : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (hr : ∀ a : F.plane, r (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a))
    (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (hs : ∀ a : F.threeSpace, s (inclusion F.threeSpace.le_normalizer a) =
      inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a))
    (g : G) (hgP : g ∈ sourcePlaneNormalizer F) (hgT : g ∈ sourceThreeSpaceNormalizer F) :
    (r ⟨g,hgP⟩ : G') * (s ⟨g,hgT⟩ : G')⁻¹ ∈ F'.plane ⊔ F'.threeSpace := by
  rw [←common_kernel_centralizer_eq_rectangle_join F']
  exact rectangle_maps_displacement_centralizes_common_kernel F F' r hr s hs g hgP hgT

end Theory.GroupTheory.TransvectionFive.UniquenessHeld

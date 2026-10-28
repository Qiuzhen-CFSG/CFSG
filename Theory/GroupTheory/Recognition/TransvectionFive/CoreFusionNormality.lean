module
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionIsolation
public import Theory.GroupTheory.UniqueFixedCosetTransvection
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRow
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceAction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionRoots

/-!
# Normality of the isolated marked root and complete local fusion alternatives

The column root acts on the row as a binary transvection whose displacement
line is the distinguished involution. A second fixed row root prevents
transitivity on the fixed subgroup. Isolation supplies unique fixed cosets,
and the marked Sylow supplies fusion control. The transvection criterion
therefore makes the row normal in the original ambient group. Simplicity
excludes this alternative in both orientations, so both noncentral root
orbits fuse to the original point. The checked rectangle census gives the
linear, Mathieu and Held local alternatives.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2.7 and Lemmas
39.9–40.5, pp.33,216–219. `FourRecognitionComplete` excludes Held using the
original affine translations and supplies the two original 12.2.27(1)
consumers. No normality or recognition callback remains.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.CoreFusion
open UniquenessLinear PlaneTensor

private theorem model_displacement (q : Model.row) :
    root (by decide : (1 : Fin 5) < 4) * (q : SL) *
      (root (by decide : (1 : Fin 5) < 4))⁻¹ * (q : SL)⁻¹ = 1 ∨
    root (by decide : (1 : Fin 5) < 4) * (q : SL) *
      (root (by decide : (1 : Fin 5) < 4))⁻¹ * (q : SL)⁻¹ = transvection := by
  let v := (modelRowCoordinates q).toAdd
  have hq : (q : SL) = rowWord (v 0) (v 1) (v 2) (v 3) :=
    (congrArg Subtype.val (modelRowCoordinates.symm_apply_apply q)).symm
  have cert : ∀ a b c d : ZMod 2,
      let t := root (by decide : (1 : Fin 5) < 4)
      let r := rowWord a b c d
      t*r*t⁻¹ = r ∨ t*r*t⁻¹ = transvection*r := by decide +kernel
  rcases cert (v 0) (v 1) (v 2) (v 3) with h | h
  · left
    rw [hq,h,mul_inv_cancel]
  · right
    rw [hq,h,mul_inv_cancel_right]

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem element32_model :
    (F.equiv ⟨element F 32,F.pullback_le _ (element_mem F 32)⟩ : SL) =
      root (by decide : (1 : Fin 5) < 4) := by
  rw [element_model]
  change modelElement (decode 32) = root (by decide : (1 : Fin 5) < 4)
  apply Subtype.ext
  rw [modelElement_matrix]
  simp [decode,val,root,Matrix.SpecialLinearGroup.transvection_coe]

/-- The literal column root has displacement in the original point line on every row element. -/
theorem column_root_displacement (x : G) (hx : x ∈ F.row) :
    element F 32*x*(element F 32)⁻¹*x⁻¹ = 1 ∨
      element F 32*x*(element F 32)⁻¹*x⁻¹ = z := by
  let H := Subgroup.centralizer ({z} : Set G)
  let t : H := ⟨element F 32,F.pullback_le _ (element_mem F 32)⟩
  let a : H := ⟨x,F.pullback_le _ hx⟩
  let q : Model.row := ⟨F.equiv a,(F.mem_pullback_iff Model.row a).mp hx⟩
  have hd := model_displacement q
  have he : (F.equiv (t*a*t⁻¹*a⁻¹) : SL) =
      root (by decide : (1 : Fin 5) < 4) * (q : SL) *
        (root (by decide : (1 : Fin 5) < 4))⁻¹ * (q : SL)⁻¹ := by
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,element32_model,t,q]
  rcases hd with hd | hd
  · left
    have hh : t*a*t⁻¹*a⁻¹ = 1 := F.equiv.injective (Subtype.ext (by
      simpa only [map_one,Subgroup.coe_one,he] using hd))
    exact congrArg Subtype.val hh
  · right
    have hh : t*a*t⁻¹*a⁻¹ = ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ :=
      F.equiv.injective (Subtype.ext (by rw [he,F.on_point]; exact hd))
    exact congrArg Subtype.val hh

/-- The displacement line is nontrivial, with an actual marked row witness. -/
theorem column_root_displacement_nontrivial :
    ∃ r ∈ F.row, element F 32*r*(element F 32)⁻¹*r⁻¹ = z := by
  let m := root (by decide : (0 : Fin 5) < 1)
  have hm : m ∈ Model.row := subset_closure ⟨1,by decide,rfl⟩
  let r := F.equiv.symm ⟨m,Model.row_le_centralizer hm⟩
  refine ⟨r,?_,?_⟩
  · apply (F.mem_pullback_iff Model.row r).mpr
    simpa only [r,F.equiv.apply_symm_apply] using hm
  · let t : Subgroup.centralizer ({z} : Set G) :=
      ⟨element F 32,F.pullback_le _ (element_mem F 32)⟩
    have hh : t*r*t⁻¹*r⁻¹ = ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ := by
      apply F.equiv.injective
      apply Subtype.ext
      simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,r,
        F.equiv.apply_symm_apply,F.on_point,element32_model,t]
      change root (by decide : (1 : Fin 5) < 4)*m*
        (root (by decide : (1 : Fin 5) < 4))⁻¹*m⁻¹ = transvection
      decide +kernel
    exact congrArg Subtype.val hh

/-- The second fixed row point is the original rectangle representative 1. -/
theorem root32_commutes_root1 : Commute (element F 32) (element F 1) := by
  let := marked_rectangle_elementary F 2
  exact setLike_mul_comm (element_mem F 32) (element_mem F 1)

variable [Finite G]

omit [Finite G] in
/-- The column representative lies outside the row under the original marking. -/
theorem root32_not_mem_row : element F 32 ∉ F.row := by
  intro h
  have hh := (UniquenessMathieu.SourceNormalizer.plane_element_mem_row_iff F 32).mp h
  exact (by decide : ¬ ((32 : PlaneCensus.Code) >>> 3 = 0)) hh

/-- Every nonidentity isolated row element has a unique fixed coset of its literal normalizer. -/
theorem row_isolation_unique_fixed (hi : RowIsolation F) :
    ∀ a ∈ F.row, a ≠ 1 → ∃! q : G ⧸ rowNormalizer F, a • q = q := by
  have hr : IsConj z (element F 1) := (hi _
    (F.row.le_normalizer (element_one_mem_row F))).mpr
      ⟨element_one_mem_row F,element_ne_one F (by decide)⟩
  have hc : ¬ IsConj z (element F 32) := fun h => root32_not_mem_row F
    ((hi _ (point_centralizer_le_row_normalizer F
      (F.pullback_le _ (element_mem F 32)))).mp h).1
  have hne := row_only_normalizer_moves F hr hc
  have hzM := F.row.le_normalizer (point_mem_row F)
  have hu : ∃! q : G ⧸ rowNormalizer F, z • q = q := by
    apply UniqueFixedCoset.unique_of_fusion_and_centralizer hzM
      (point_centralizer_le_row_normalizer F)
    intro g hg
    have hf : IsConj z (g*z*g⁻¹) := isConj_iff.mpr ⟨g,rfl⟩
    obtain ⟨haA,ha1⟩ := (hi _ hg).mp hf
    let p : F.row := ⟨z,point_mem_row F⟩
    let q : F.row := ⟨g*z*g⁻¹,haA⟩
    obtain ⟨f,hf⟩ := row_aut_transitive F p q
      (fun h => point_ne_one F (congrArg Subtype.val h))
      (fun h => ha1 (congrArg Subtype.val h))
    obtain ⟨m,hm⟩ := row_action_surjective_of_normalizer_ne_centralizer F hne f
    refine ⟨m,m.property,?_⟩
    have he := congrArg Subtype.val ((congrArg (fun f : MulAut F.row => f p) hm).trans hf)
    exact he.symm
  intro a ha ha1
  exact UniqueFixedCoset.unique_of_isConj hu ((hi a (F.row.le_normalizer ha)).mpr ⟨ha,ha1⟩)

/-- Source 39.9: the actual isolated root subgroup is normal in the ambient group. -/
theorem row_isolation_normal (hi : RowIsolation F) : F.row.Normal := by
  let := source_row_elementary F
  have htM : element F 32 ∈ rowNormalizer F :=
    point_centralizer_le_row_normalizer F (F.pullback_le _ (element_mem F 32))
  have ht2 : orderOf (element F 32) = 2 := by
    let := marked_rectangle_elementary F 2
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ (element_mem F 32))
      (element_ne_one F (by decide))
  have hu := row_isolation_unique_fixed F hi
  apply normalizer_eq_top_iff.mp
  apply UniqueFixedCoset.normalizer_eq_top_of_binary_displacement F.row hu z
    (element F 32) (element F 1) (point_mem_row F) (element_one_mem_row F)
    (point_ne_one F) (element_ne_one F (by decide)) (Ne.symm (element_one_ne_point F))
    ((mem_centralizer_singleton_iff.mp (F.pullback_le _ (element_mem F 32))).symm)
    (root32_commutes_root1 F).symm htM (root32_not_mem_row F) ht2
  · intro y hy hf
    have hTM := (sourceSylow_le_point_centralizer F).trans
      (point_centralizer_le_row_normalizer F)
    have hzT := (flag_le_sourceSylow F).1 (point_mem_row F)
    have htP : IsPGroup 2 (zpowers (element F 32)) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,ht2,pow_one])
    exact UniqueFixedCoset.p_element_fusion (sourceSylow F) hTM hzT
      (fun s hs => (mem_centralizer_singleton_iff.mp
        (sourceSylow_le_point_centralizer F hs)).symm)
      (hu z (point_mem_row F) (point_ne_one F)) htM hy htP hf
  · exact column_root_displacement F
  · exact column_root_displacement_nontrivial F

/-- The two root orbits fuse in a finite simple group with the original point-core fusion. -/
theorem root_fusion (hG : IsSimpleGroup G) (hcore : PointCoreFusion z) :
    IsConj z (element F 1) ∧ IsConj z (element F 32) := by
  have hd := root_fusion_disjunction F hcore
  by_cases hr : IsConj z (element F 1)
  · refine ⟨hr,?_⟩
    by_contra hc
    exact not_row_normal F hG hcore (row_isolation_normal F (row_only_isolation F hr hc))
  · have hc := hd.resolve_left hr
    exact (not_row_normal (oppositeMarking F) hG hcore
      (row_isolation_normal (oppositeMarking F) (row_only_isolation (oppositeMarking F)
        ((opposite_root_fusion F).1.mpr hc)
        (fun h => hr ((opposite_root_fusion F).2.mp h))))).elim

/-- The complete source §§39–40 local type alternative, with no normality callback. -/
theorem local_fusion_alternatives (hG : IsSimpleGroup G) (hcore : PointCoreFusion z) :
    F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern :=
  alternatives_of_isolation_normality F hG hcore (fun _ E => row_isolation_normal E)

end Theory.GroupTheory.TransvectionFive.CoreFusion

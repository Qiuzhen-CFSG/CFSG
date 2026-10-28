module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersectionAction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersectionKernel
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceEdgePerfect
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms

/-!
# Compatible marked maps on the literal source overlap

An automorphism of `I = N_G(row) ∩ N_G(threeSpace)` fixing the distinguished
involution is inner, by combining its realized action on the characteristic
rectangle with the pointwise-kernel calculation. This marked statement is
sufficient here: both original local comparisons send z to the same target
mark. Their restrictions therefore differ by conjugation by an element of
the target I. Correcting the three-space comparison by that conjugation
makes the two maps agree on every element of the common intersection.

The row comparison retains the point–line intersection, the whole pointwise
edge fixer, and the three-space intersection. The corrected three-space
comparison retains its row intersection. The final theorem applies these
maps inside the original normalizer-generated subgroup without assuming
simplicity. These are the pointwise alignment steps of Aschbacher,
*Sporadic Groups* (1994), 41.3–41.4, printed p.222.

The marked innerness theorem is not a claim that every automorphism of I
fixes z. Native-system identification, the local setwise-edge condition,
and ambient generation remain necessary for `SourceComparison`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

include hlinear in
/-- The marked form of 41.3 needed by the actual two restrictions. -/
theorem intersection_point_automorphism_inner
    (a : MulAut (rowThreeIntersection F))
    (ha : a ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩ =
      ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩) :
    ∃ c : rowThreeIntersection F,
      (c : G) ∈ Subgroup.centralizer ({z} : Set G) ∧ a = MulAut.conj c := by
  obtain ⟨c, hc, he⟩ := intersection_point_action F hlinear a ha
  let b : MulAut (rowThreeIntersection F) := a.trans (MulAut.conj c⁻¹)
  have hb (x : F.threeSpace.subgroupOf (rowThreeIntersection F)) : b x = x := by
    change c⁻¹ * a x * (c⁻¹)⁻¹ = x
    rw [he]
    group
  obtain ⟨u, hu⟩ := intersection_fixed_kernel_inner F hlinear b hb
  refine ⟨c * u, ?_, ?_⟩
  · exact (Subgroup.centralizer _).mul_mem hc (F.pullback_le _ u.property)
  · apply MulEquiv.ext
    intro x
    have hx := congrArg (fun f : MulAut (rowThreeIntersection F) => f x) hu
    change c⁻¹ * a x * (c⁻¹)⁻¹ = (u : rowThreeIntersection F) * x * (u : rowThreeIntersection F)⁻¹ at hx
    change a x = (c * u) * x * (c * u)⁻¹
    calc
      _ = c * (c⁻¹ * a x * (c⁻¹)⁻¹) * c⁻¹ := by group
      _ = _ := by rw [hx]; group

end Theory.GroupTheory.TransvectionFive.UniquenessLinear

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open SourceGeometry
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')
  (hlinear : F.LinearFusion) (hlinear' : F'.LinearFusion)

omit [Finite G] [Finite G'] in
theorem planeMarkingEquiv_point :
    planeMarkingEquiv F F' ⟨z, point_mem_plane F⟩ = ⟨z', point_mem_plane F'⟩ := by
  have h := planeMarkingEquiv_element F F' 4
  have hp (E : MarkedCentralizer z) : PlaneTensor.sourceEquiv E 4 = ⟨z, point_mem_plane E⟩ :=
    Subtype.ext (PlaneTensor.element_point E)
  rw [hp] at h
  exact h.trans (Subtype.ext (PlaneTensor.element_point F'))

omit [Finite G] [Finite G'] in
theorem rowMarkingEquiv_point :
    rowMarkingEquiv F F' ⟨z, point_mem_row F⟩ = ⟨z', point_mem_row F'⟩ := by
  apply (F'.pullbackEquiv Model.row Model.row_le_centralizer).injective
  rw [rowMarkingEquiv_model]
  apply Subtype.ext
  change (F.equiv ⟨z, _⟩ : SL) = (F'.equiv ⟨z', _⟩ : SL)
  rw [F.on_point, F'.on_point]

omit [Finite G] [Finite G'] in
private theorem transport_point_flag
    {A B I J : Subgroup G} {A' B' I' J' : Subgroup G'}
    (hAB : A = B) (hAB' : A' = B') (hIJ : I = J) (hIJ' : I' = J')
    (hzA : z ∈ A) (hzA' : z' ∈ A') (hzB : z ∈ B) (hzB' : z' ∈ B')
    (he : ∃ e : A ≃* A', (I.subgroupOf A).map e.toMonoidHom = I'.subgroupOf A' ∧
      e ⟨z, hzA⟩ = ⟨z', hzA'⟩) :
    ∃ e : B ≃* B', (J.subgroupOf B).map e.toMonoidHom = J'.subgroupOf B' ∧
      e ⟨z, hzB⟩ = ⟨z', hzB'⟩ := by
  subst B
  subst B'
  subst J
  subst J'
  exact he

include hlinear hlinear' in
/-- Retain the common-intersection image and the original distinguished point. -/
theorem exists_threeSpace_normalizer_point_flag_equiv :
    ∃ e : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F',
      ((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map e.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') ∧
      e ⟨z, F.threeSpace.le_normalizer (point_mem_threeSpace F)⟩ =
        ⟨z', F'.threeSpace.le_normalizer (point_mem_threeSpace F')⟩ := by
  let E := oppositeMarking F
  let E' := oppositeMarking F'
  have h := exists_plane_normalizer_equiv E E'
    (oppositeMarking_linearFusion F hlinear) (oppositeMarking_linearFusion F' hlinear')
  obtain ⟨e, he, _⟩ := h
  have hf := plane_normalizer_equiv_column_intersection E E'
    (oppositeMarking_linearFusion F hlinear) (oppositeMarking_linearFusion F' hlinear') e he
  have hp : e ⟨z, E.plane.le_normalizer (point_mem_plane E)⟩ =
      ⟨z', E'.plane.le_normalizer (point_mem_plane E')⟩ := by
    have h := he ⟨z, point_mem_plane E⟩
    rw [planeMarkingEquiv_point] at h
    exact h
  exact transport_point_flag
    (congrArg (fun A : Subgroup G => normalizer (A : Set G)) (oppositeMarking_plane F))
    (congrArg (fun A : Subgroup G' => normalizer (A : Set G')) (oppositeMarking_plane F'))
    (congrArg (fun A : Subgroup G => normalizer (A : Set G)) (oppositeMarking_column F))
    (congrArg (fun A : Subgroup G' => normalizer (A : Set G')) (oppositeMarking_column F'))
    _ _ _ _ ⟨e, hf, hp⟩

/-- The row comparison preserves both flag intersections, the edge fixer, and z. -/
theorem exists_row_normalizer_point_edge_flag_equiv :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((edgeGroup F hlinear).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (edgeGroup F' hlinear').subgroupOf (rowNormalizer F')) ∧
      e ⟨z, F.row.le_normalizer (point_mem_row F)⟩ =
        ⟨z', F'.row.le_normalizer (point_mem_row F')⟩ := by
  obtain ⟨e, he, hP, hH, _⟩ := exists_row_normalizer_flag_equiv F F' hlinear hlinear'
  refine ⟨e, hP, hH, row_equiv_edgeGroup F hlinear F' hlinear' e hP, ?_⟩
  have h := he ⟨z, point_mem_row F⟩
  rw [rowMarkingEquiv_point] at h
  exact h

end Theory.GroupTheory.TransvectionFive.UniquenessLinear

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open SourceGeometry

private def infEquivSubgroupOf {G : Type*} [Group G] (A B : Subgroup G) :
    (A ⊓ B : Subgroup G) ≃* B.subgroupOf A where
  toFun x := ⟨⟨x, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def restrictInf {G G' : Type*} [Group G] [Group G']
    {A B : Subgroup G} {A' B' : Subgroup G'} (e : A ≃* A')
    (h : (B.subgroupOf A).map e.toMonoidHom = B'.subgroupOf A') :
    (A ⊓ B : Subgroup G) ≃* (A' ⊓ B' : Subgroup G') :=
  (infEquivSubgroupOf A B).trans ((e.subgroupMap (B.subgroupOf A)).trans
    ((MulEquiv.subgroupCongr h).trans (infEquivSubgroupOf A' B').symm))

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')
  (hlinear : F.LinearFusion) (hlinear' : F'.LinearFusion)

omit [Finite G] in
include hlinear' in
/-- Correct the local map by a target intersection element to agree pointwise. -/
theorem align_local_maps
    (r : rowNormalizer F ≃* rowNormalizer F')
    (hr : ((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
      (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F'))
    (hrz : r ⟨z, F.row.le_normalizer (point_mem_row F)⟩ =
      ⟨z', F'.row.le_normalizer (point_mem_row F')⟩)
    (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (hs : ((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map s.toMonoidHom =
      (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F'))
    (hsz : s ⟨z, F.threeSpace.le_normalizer (point_mem_threeSpace F)⟩ =
      ⟨z', F'.threeSpace.le_normalizer (point_mem_threeSpace F')⟩) :
    ∃ t : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F',
      (((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map t.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F')) ∧
      ∀ (g : G) (hgR : g ∈ rowNormalizer F) (hgS : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hgR⟩ : G') = (t ⟨g, hgS⟩ : G') := by
  let rI : rowThreeIntersection F ≃* rowThreeIntersection F' := restrictInf r hr
  let sI : rowThreeIntersection F ≃* rowThreeIntersection F' :=
    (MulEquiv.subgroupCongr (inf_comm _ _)).trans
      ((restrictInf s hs).trans (MulEquiv.subgroupCongr (inf_comm _ _)))
  let p : rowThreeIntersection F :=
    ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩
  let p' : rowThreeIntersection F' :=
    ⟨z', threeSpace_le_rowThreeIntersection F' (point_mem_threeSpace F')⟩
  have hrp : rI p = p' := Subtype.ext (congrArg (fun x : rowNormalizer F' => (x : G')) hrz)
  have hsp : sI p = p' := Subtype.ext (congrArg (fun x : sourceThreeSpaceNormalizer F' => (x : G')) hsz)
  let a : MulAut (rowThreeIntersection F') := sI.symm.trans rI
  have hap : a p' = p' := by
    change rI (sI.symm p') = p'
    rw [← hsp, sI.symm_apply_apply, hrp]
    exact hsp.symm
  obtain ⟨c, _, hc⟩ := intersection_point_automorphism_inner F' hlinear' a hap
  let d : sourceThreeSpaceNormalizer F' := ⟨c, c.property.2⟩
  let t := s.trans (MulAut.conj d)
  refine ⟨t, ?_, fun g hgR hgS => ?_⟩
  · change ((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map
      ((MulAut.conj d).toMonoidHom.comp s.toMonoidHom) = _
    rw [← map_map, hs]
    apply mem_normalizer_iff_map_conj_eq.mp
    exact ((rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F')).le_normalizer c.property.1
  · let x : rowThreeIntersection F := ⟨g, hgR, hgS⟩
    have he := congrArg (fun e : MulAut (rowThreeIntersection F') => e (sI x)) hc
    change rI (sI.symm (sI x)) = c * sI x * c⁻¹ at he
    rw [sI.symm_apply_apply] at he
    exact congrArg (fun x : rowThreeIntersection F' => (x : G')) he

/-- Both literal local maps with their entire overlap restrictions aligned. -/
theorem exists_compatible_local_maps :
    ∃ (r : rowNormalizer F ≃* rowNormalizer F')
      (t : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F'),
      (((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((edgeGroup F hlinear).subgroupOf (rowNormalizer F)).map r.toMonoidHom =
        (edgeGroup F' hlinear').subgroupOf (rowNormalizer F')) ∧
      (((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map t.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F')) ∧
      ∀ (g : G) (hgR : g ∈ rowNormalizer F) (hgS : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g, hgR⟩ : G') = (t ⟨g, hgS⟩ : G') := by
  obtain ⟨r, hP, hS, hE, hr⟩ := exists_row_normalizer_point_edge_flag_equiv F F' hlinear hlinear'
  obtain ⟨s, hR, hs⟩ := exists_threeSpace_normalizer_point_flag_equiv F F' hlinear hlinear'
  obtain ⟨t, ht, ha⟩ := align_local_maps F F' hlinear' r hS hr s hR hs
  exact ⟨r, t, hP, hS, hE, ht, ha⟩

/-- The actual 41.1 induction subgroup has the same compatible comparisons;
its fusion premises are inherited and discharged, with no simplicity input. -/
theorem normalizerSpan_compatible_local_maps :
    ∃ (r : rowNormalizer (normalizerSpanMarking F) ≃* rowNormalizer F')
      (t : sourceThreeSpaceNormalizer (normalizerSpanMarking F) ≃*
        sourceThreeSpaceNormalizer F'),
      (((sourcePlaneNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map r.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((sourceThreeSpaceNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map r.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F')) ∧
      (((edgeGroup (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map r.toMonoidHom =
        (edgeGroup F' hlinear').subgroupOf (rowNormalizer F')) ∧
      (((rowNormalizer (normalizerSpanMarking F)).subgroupOf
        (sourceThreeSpaceNormalizer (normalizerSpanMarking F))).map t.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F')) ∧
      ∀ (g : normalizerSpan F) (hgR : g ∈ rowNormalizer (normalizerSpanMarking F))
        (hgS : g ∈ sourceThreeSpaceNormalizer (normalizerSpanMarking F)),
        (r ⟨g, hgR⟩ : G') = (t ⟨g, hgS⟩ : G') :=
  exists_compatible_local_maps (normalizerSpanMarking F) F'
    (normalizerSpan_linearFusion F hlinear) hlinear'

end Theory.GroupTheory.TransvectionFive.UniquenessLinear

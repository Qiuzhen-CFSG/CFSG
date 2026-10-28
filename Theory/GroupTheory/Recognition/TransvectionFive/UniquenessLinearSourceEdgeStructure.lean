module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceEdgeFixer
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.ThreeSpace
public import Theory.GroupTheory.GraphUniquenessSystem.OddIndexRigidity
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct

/-!
# The actual source edge-fixer quotient

Line uniqueness identifies the ambient edge fixer with the kernel of the
three-point line action. Its remaining tensor factor gives a surjection to
GL₃(2) with kernel the literal A₁. The quotient map and conjugation on both
tensor rows are retained. Normalizing this edge fixer inside N_G(U₁) is
exactly preserving the marked point–line flag.

These are the edge-group and intersection ingredients in Aschbacher,
*Sporadic Groups* (1994), 41.4, printed p.222. No ambient comparison or
recognition conclusion is assumed.
-/

public noncomputable section
open Subgroup Module
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open PlaneTensor PlaneCensus
open UniquenessMathieu.OctadSource
  (plane_element_mem_threeSpace_iff tensor_decomposition tensor_intersection)
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

/-- The actual pointwise fixer of the marked source edge. -/
abbrev edgeGroup := edgeFixer G (vertex (rowNormalizer F) 1)
  (vertex (rowNormalizer F) (lineSwap F hlinear : G))

/-- The first rectangle lies in the actual edge fixer. -/
theorem rectangle_le_edgeGroup : F.plane ≤ edgeGroup F hlinear := by
  intro a ha
  apply (line_edgeFixer_iff F hlinear ⟨a, F.plane.le_normalizer ha⟩).mpr
  have hq : (QuotientGroup.mk (⟨a, F.plane.le_normalizer ha⟩ : sourcePlaneNormalizer F) :
      sourcePlaneQuotient F) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
  change (linearPlaneQuotientEquiv F hlinear _).2 = 1
  change (linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk (⟨a, F.plane.le_normalizer ha⟩ : sourcePlaneNormalizer F))).2 = 1
  rw [hq, map_one]
  rfl

/-- The full ambient edge fixer acts by its actual three-dimensional tensor factor. -/
@[expose] def edgeLinearAction : edgeGroup F hlinear →*
    ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  (MonoidHom.fst _ _).comp (((linearPlaneQuotientEquiv F hlinear).toMonoidHom.comp
    (QuotientGroup.mk' _)).comp (inclusion (edgeFixer_le_line F hlinear)))

/-- The literal rectangle quotient of an edge element has trivial line permutation. -/
theorem edge_tensor_image (a : edgeGroup F hlinear) :
    linearPlaneQuotientEquiv F hlinear
      (QuotientGroup.mk (inclusion (edgeFixer_le_line F hlinear) a)) =
        (edgeLinearAction F hlinear a, 1) := by
  apply Prod.ext
  · rfl
  · exact (line_edgeFixer_iff F hlinear _).mp a.property

/-- The induced action on the first tensor factor is onto GL₃(2). -/
theorem edgeLinearAction_surjective : Function.Surjective (edgeLinearAction F hlinear) := by
  intro f
  obtain ⟨q, hq⟩ := (linearPlaneQuotientEquiv F hlinear).surjective (f, 1)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  have he : (n : G) ∈ edgeGroup F hlinear := (line_edgeFixer_iff F hlinear n).mpr (congrArg Prod.snd hq)
  exact ⟨⟨n, he⟩, congrArg Prod.fst hq⟩

/-- The kernel is the original A₁, retaining its literal inclusion in the edge fixer. -/
theorem edgeLinearAction_kernel :
    (edgeLinearAction F hlinear).ker = F.plane.subgroupOf (edgeGroup F hlinear) := by
  ext a
  change edgeLinearAction F hlinear a = 1 ↔ (a : G) ∈ F.plane
  have he : edgeLinearAction F hlinear a = 1 ↔
      linearPlaneQuotientEquiv F hlinear
        (QuotientGroup.mk (inclusion (edgeFixer_le_line F hlinear) a)) = 1 := by
    rw [edge_tensor_image]
    exact ⟨fun h => Prod.ext h rfl, fun h => congrArg Prod.fst h⟩
  rw [he, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  rfl

instance rectangle_normal_edge : (F.plane.subgroupOf (edgeGroup F hlinear)).Normal :=
  normal_subgroupOf_of_le_normalizer (edgeFixer_le_line F hlinear)

/-- The actual edge-fixer quotient is GL₃(2), with its original denominator. -/
def edgeQuotientEquiv :
    (edgeGroup F hlinear ⧸ F.plane.subgroupOf (edgeGroup F hlinear)) ≃*
      ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (edgeLinearAction_kernel F hlinear).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (edgeLinearAction F hlinear)
      (edgeLinearAction_surjective F hlinear))

@[simp] theorem edgeQuotientEquiv_mk (a : edgeGroup F hlinear) :
    edgeQuotientEquiv F hlinear (QuotientGroup.mk a) = edgeLinearAction F hlinear a := by rfl

/-- Both tensor rows retain the same original conjugation action of the edge fixer. -/
theorem edgeLinearAction_tensor (a : edgeGroup F hlinear) (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode i (edgeLinearAction F hlinear a v)) =
      (a : G) * element F (tensorCode i v) * (a : G)⁻¹ := by
  have he := lineAction_tensor F hlinear (inclusion (edgeFixer_le_line F hlinear) a) i v
  have hp := (line_edgeFixer_iff F hlinear (inclusion (edgeFixer_le_line F hlinear) a)).mp a.property
  rw [hp] at he
  exact he

@[expose] def edgePlaneSubspace : Submodule (ZMod 2) (Fin 3 → ZMod 2) where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by intro a b ha hb; change a 0 + b 0 = 0; rw [ha, hb, zero_add]
  smul_mem' := by intro c v hv; change c * v 0 = 0; rw [hv, mul_zero]



omit [Finite G] in
/-- The plane intersection is the same two-space in each tensor direction. -/
theorem tensor_element_mem_threeSpace_iff (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (tensorCode i v) ∈ F.threeSpace ↔ v ∈ edgePlaneSubspace := by
  rw [plane_element_mem_threeSpace_iff]
  exact tensor_intersection i v

/-- Preserving the literal two-space in the three-dimensional tensor factor
preserves the actual source plane. -/
theorem line_linear_parabolic_mem_plane (n : sourcePlaneNormalizer F)
    (hn : (linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 ∈
      BinaryLinear.parabolic edgePlaneSubspace) : (n : G) ∈ sourceThreeSpaceNormalizer F := by
  have hI : (n : G) ∈ normalizer ((F.plane ⊓ F.threeSpace : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.1⟩
      have hxa : element F x = a := congrArg Subtype.val hx
      obtain ⟨v, w, hvw, hzero⟩ := tensor_decomposition x
      have hz := hzero.mp ((plane_element_mem_threeSpace_iff F x).mp (hxa.symm ▸ ha.2))
      have he : (n : G) * a * (n : G)⁻¹ =
          element F (tensorCode (lineAction F hlinear n 0)
            ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 v)) *
          element F (tensorCode (lineAction F hlinear n 1)
            ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 w)) := by
        rw [← hxa, ← hvw, element_xor, lineAction_tensor, lineAction_tensor]
        group
      refine ⟨(mem_normalizer_iff.mp n.property a).mp ha.1, ?_⟩
      change (n : G) * a * (n : G)⁻¹ ∈ F.threeSpace
      rw [he]
      exact F.threeSpace.mul_mem
        ((tensor_element_mem_threeSpace_iff F _ _).mpr ((hn v).mpr hz.1))
        ((tensor_element_mem_threeSpace_iff F _ _).mpr ((hn w).mpr hz.2))
    · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
  rw [planes_intersection_normalizer F] at hI
  exact hI.2

private theorem line_plane_preserves (n : sourcePlaneNormalizer F) (hn : (n : G) ∈ sourceThreeSpaceNormalizer F)
    (v : Fin 3 → ZMod 2) (hv : v ∈ edgePlaneSubspace) :
    (linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 v ∈ edgePlaneSubspace := by
  have ha := (mem_normalizer_iff.mp hn (element F (tensorCode 0 v))).mp
    ((tensor_element_mem_threeSpace_iff F 0 v).mpr hv)
  rw [← lineAction_tensor F hlinear n] at ha
  exact (tensor_element_mem_threeSpace_iff F _ _).mp ha

/-- The line–plane flag is exactly the parabolic of the marked tensor two-space. -/
theorem line_mem_plane_iff (n : sourcePlaneNormalizer F) :
    (n : G) ∈ sourceThreeSpaceNormalizer F ↔
      (linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 ∈
        BinaryLinear.parabolic edgePlaneSubspace := by
  constructor
  · intro hn v
    constructor
    · intro hv
      have hh := line_plane_preserves F hlinear n⁻¹ ((sourceThreeSpaceNormalizer F).inv_mem hn)
        ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 v) hv
      have hi : (QuotientGroup.mk n⁻¹ : sourcePlaneQuotient F) = (QuotientGroup.mk n)⁻¹ :=
        by rfl
      rw [hi, map_inv] at hh
      change ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1).symm
        ((linearPlaneQuotientEquiv F hlinear (QuotientGroup.mk n)).1 v) ∈ edgePlaneSubspace at hh
      rwa [LinearEquiv.symm_apply_apply] at hh
    · exact line_plane_preserves F hlinear n hn v
  · exact line_linear_parabolic_mem_plane F hlinear n

/-- In the actual edge group, plane stabilization is the marked tensor parabolic. -/
theorem edge_mem_plane_iff (a : edgeGroup F hlinear) :
    (a : G) ∈ sourceThreeSpaceNormalizer F ↔
      edgeLinearAction F hlinear a ∈ BinaryLinear.parabolic edgePlaneSubspace :=
  line_mem_plane_iff F hlinear (inclusion (edgeFixer_le_line F hlinear) a)

/-- The actual edge–plane intersection is the preimage through the literal action. -/
theorem edge_plane_parabolic_comap :
    (BinaryLinear.parabolic edgePlaneSubspace).comap (edgeLinearAction F hlinear) =
      (sourceThreeSpaceNormalizer F).subgroupOf (edgeGroup F hlinear) := by
  ext a
  exact (edge_mem_plane_iff F hlinear a).symm

include hlinear in
/-- The first rectangle is contained in the plane normalizer as an actual subgroup. -/
theorem rectangle_le_plane_normalizer : F.plane ≤ sourceThreeSpaceNormalizer F := by
  intro a ha
  let b : edgeGroup F hlinear := ⟨a, rectangle_le_edgeGroup F hlinear ha⟩
  apply (edge_mem_plane_iff F hlinear b).mpr
  have hk : b ∈ (edgeLinearAction F hlinear).ker := by
    rw [edgeLinearAction_kernel]
    exact ha
  rw [show edgeLinearAction F hlinear b = 1 from hk]
  exact Subgroup.one_mem _


private def planeSubspaceEquiv : edgePlaneSubspace ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v i := v.val i.succ
  invFun v := ⟨Fin.cases 0 v, by rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact v.property.symm
    · rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal tensor intersection is a two-dimensional hyperplane. -/
theorem edgePlaneSubspace_finrank : finrank (ZMod 2) edgePlaneSubspace = 2 := by
  rw [planeSubspaceEquiv.finrank_eq]
  simp



/-- The actual local edge fixer has odd index seven in the full edge fixer. -/
theorem edge_plane_index : (sourceThreeSpaceNormalizer F).relIndex (edgeGroup F hlinear) = 7 := by
  change ((sourceThreeSpaceNormalizer F).subgroupOf (edgeGroup F hlinear)).index = _
  rw [← edge_plane_parabolic_comap F hlinear, index_comap_of_surjective _ (edgeLinearAction_surjective F hlinear)]
  exact BinaryLinear.FourParabolicAction.threeSpace_hyperplane_index _ (by simp)
    edgePlaneSubspace_finrank

private theorem tensor_pair_injective : Function.Injective
    (fun p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) =>
      tensorCode 0 p.1 ^^^ tensorCode 1 p.2) := by decide

/-- The actual plane–edge intersection fixes no nonidentity element of A₁. -/
theorem edge_plane_fixed_rectangle (a : F.plane)
    (ha : ∀ n : edgeGroup F hlinear, (n : G) ∈ sourceThreeSpaceNormalizer F →
      (n : G) * (a : G) * (n : G)⁻¹ = a) : a = 1 := by
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective a
  have hxa : element F x = (a : G) := congrArg Subtype.val hx
  obtain ⟨v, w, hvw, _⟩ := tensor_decomposition x
  have hfixed (f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (hf : f ∈ BinaryLinear.parabolic edgePlaneSubspace) : f v = v ∧ f w = w := by
    obtain ⟨n, hn⟩ := edgeLinearAction_surjective F hlinear f
    have hnH : (n : G) ∈ sourceThreeSpaceNormalizer F :=
      (edge_mem_plane_iff F hlinear n).mpr (hn.symm ▸ hf)
    have he : element F (tensorCode 0 (f v) ^^^ tensorCode 1 (f w)) =
        element F (tensorCode 0 v ^^^ tensorCode 1 w) := by
      rw [element_xor, ← hn, edgeLinearAction_tensor, edgeLinearAction_tensor]
      calc
        _ = (n : G) * (element F (tensorCode 0 v) * element F (tensorCode 1 w)) *
            (n : G)⁻¹ := by group
        _ = (n : G) * (a : G) * (n : G)⁻¹ := by rw [← element_xor, hvw, hxa]
        _ = a := ha n hnH
        _ = _ := by rw [hvw, hxa]
    exact Prod.mk.inj (tensor_pair_injective (element_injective F he))
  have hv := BinaryLinear.FourParabolicAction.threeSpace_hyperplane_fixed edgePlaneSubspace
    (by simp) edgePlaneSubspace_finrank v (fun f hf => (hfixed f hf).1)
  have hw := BinaryLinear.FourParabolicAction.threeSpace_hyperplane_fixed edgePlaneSubspace
    (by simp) edgePlaneSubspace_finrank w (fun f hf => (hfixed f hf).2)
  have hx0 : x = 0 := by
    rw [← hvw, hv, hw]
    decide
  apply Subtype.ext
  rw [← hxa, hx0, element_zero]
  rfl

/-- The exact rigidity required by Theorem 37.9 for the literal source groups. -/
theorem edge_plane_automorphismRigid :
    AutomorphismRigid ((sourceThreeSpaceNormalizer F).subgroupOf (edgeGroup F hlinear)) := by
  let B := edgeGroup F hlinear
  let N := F.plane.subgroupOf B
  let J := (sourceThreeSpaceNormalizer F).subgroupOf B
  let := marked_rectangle_elementary F 2
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (rectangle_le_edgeGroup F hlinear)).toMonoidHom
    (subgroupOfEquivOfLe (rectangle_le_edgeGroup F hlinear)).injective
  apply automorphismRigid_of_odd_index N J
  · exact fun a ha => rectangle_le_plane_normalizer F hlinear ha
  · intro a ha
    change (a : G) ∈ F.plane
    rw [← source_plane_centralizer F]
    apply mem_centralizer_iff.mpr
    intro b hb
    have hh := mem_centralizer_iff.mp ha
      (⟨b, rectangle_le_edgeGroup F hlinear hb⟩ : B) hb
    exact congrArg Subtype.val hh
  · intro n
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 N) n
  · change Odd ((sourceThreeSpaceNormalizer F).relIndex (edgeGroup F hlinear))
    rw [edge_plane_index]
    decide
  · apply eq_bot_iff.mpr
    rintro a ⟨haN, haJ⟩
    have he : (⟨(a : G), haN⟩ : F.plane) = 1 := edge_plane_fixed_rectangle F hlinear _ (by
      intro n hn
      have hh := mem_centralizer_iff.mp haJ n hn
      have hg := congrArg (fun b : B => (b : G)) hh
      change (n : G) * (a : G) = (a : G) * (n : G) at hg
      rw [hg, mul_inv_cancel_right])
    change a = 1
    exact Subtype.ext (congrArg (fun x : F.plane => (x : G)) he)


/-- The local edge fixer's normalizer in the point–plane intersection is
exactly the original point–line–plane flag stabilizer, as in 41.4 (V4). -/
theorem local_edgeFixer_normalizer :
    normalizer ((sourceThreeSpaceNormalizer F ⊓ edgeGroup F hlinear : Subgroup G) : Set G) ⊓
      (rowNormalizer F ⊓ sourceThreeSpaceNormalizer F) =
        sourcePlaneNormalizer F ⊓ (rowNormalizer F ⊓ sourceThreeSpaceNormalizer F) := by
  have hrH : F.row ≤ sourceThreeSpaceNormalizer F :=
    (flag_le_sourceSylow F).1.trans (plane_normalizers_contain_sourceSylow F).2
  have hi : F.row ⊓ (sourceThreeSpaceNormalizer F ⊓ edgeGroup F hlinear) =
      F.row ⊓ F.plane := by
    rw [← inf_assoc, inf_eq_left.mpr hrH]
    exact row_edgeFixer_intersection F hlinear
  apply le_antisymm
  · rintro n ⟨hn, hr, hH⟩
    have h := inf_normalizer_le_normalizer_inf ⟨hr, hn⟩
    rw [hi, source_row_plane_normalizer] at h
    exact ⟨h.2, hr, hH⟩
  · rintro n ⟨hP, hr, hH⟩
    exact ⟨inf_normalizer_le_normalizer_inf
      ⟨(sourceThreeSpaceNormalizer F).le_normalizer hH,
        line_normalizes_edgeFixer F hlinear hP⟩, hr, hH⟩

/-- The precise normalizer inclusion in the similarity criterion of §37
holds for the literal local source edge fixer. -/
theorem local_edgeFixer_normalizer_le :
    normalizer ((sourceThreeSpaceNormalizer F ⊓ edgeGroup F hlinear : Subgroup G) : Set G) ⊓
      (rowNormalizer F ⊓ sourceThreeSpaceNormalizer F) ≤
        normalizer (edgeGroup F hlinear : Set G) := by
  rw [local_edgeFixer_normalizer]
  exact inf_le_left.trans (line_normalizes_edgeFixer F hlinear)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry

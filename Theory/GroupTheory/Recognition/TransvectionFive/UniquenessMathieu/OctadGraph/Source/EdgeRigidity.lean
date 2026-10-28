module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgePlane
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.ThreeSpace
public import Theory.GroupTheory.GraphUniquenessSystem.OddIndexRigidity
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-!
# Rigidity of the actual Mathieu source edge fixer

The intersection with the plane normalizer has index seven in the edge
fixer, through its literal tensor quotient. Its action on each natural
three-space is a hyperplane parabolic and has zero fixed space. Thus it
centralizes no nonidentity rectangle element. Since the rectangle is
self-centralizing, odd-index crossed-homomorphism averaging proves that
an automorphism fixing this intersection pointwise is the identity.

This discharges the precise rigidity premise in the 37.9 application of
Aschbacher, *Sporadic Groups* (1994), 41.4, p.222. Only the earlier
SourceNormalizer.LocalData are assumed. The internal imports reuse the
checked tensor decomposition; the 64-element tensor-pair encoding is used
only to prove uniqueness of its two coordinates.
-/

public noncomputable section
open Subgroup Module
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
open GraphUniquenessSystem GraphUniquenessSystem.Cosets

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

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- The actual local edge fixer has odd index seven in the full edge fixer. -/
theorem edge_plane_index : (threeSpaceNormalizer F).relIndex (edgeGroup F D) = 7 := by
  change ((threeSpaceNormalizer F).subgroupOf (edgeGroup F D)).index = _
  rw [← edge_plane_parabolic_comap F D, index_comap_of_surjective _ (edgeLinearAction_surjective F D)]
  exact BinaryLinear.FourParabolicAction.threeSpace_hyperplane_index _ (by simp)
    edgePlaneSubspace_finrank

private theorem tensor_pair_injective : Function.Injective
    (fun p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) =>
      tensorCode 0 p.1 ^^^ tensorCode 1 p.2) := by decide

/-- The actual plane–edge intersection fixes no nonidentity element of A₁. -/
theorem edge_plane_fixed_rectangle (a : F.plane)
    (ha : ∀ n : edgeGroup F D, (n : G) ∈ threeSpaceNormalizer F →
      (n : G) * (a : G) * (n : G)⁻¹ = a) : a = 1 := by
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective a
  have hxa : element F x = (a : G) := congrArg Subtype.val hx
  obtain ⟨v, w, hvw, _⟩ := tensor_decomposition x
  have hfixed (f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (hf : f ∈ BinaryLinear.parabolic edgePlaneSubspace) : f v = v ∧ f w = w := by
    obtain ⟨n, hn⟩ := edgeLinearAction_surjective F D f
    have hnH : (n : G) ∈ threeSpaceNormalizer F :=
      (edge_mem_plane_iff F D n).mpr (hn.symm ▸ hf)
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
    AutomorphismRigid ((threeSpaceNormalizer F).subgroupOf (edgeGroup F D)) := by
  let B := edgeGroup F D
  let N := F.plane.subgroupOf B
  let J := (threeSpaceNormalizer F).subgroupOf B
  let := marked_rectangle_elementary F 2
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (rectangle_le_edgeGroup F D)).toMonoidHom
    (subgroupOfEquivOfLe (rectangle_le_edgeGroup F D)).injective
  apply automorphismRigid_of_odd_index N J
  · exact fun a ha => rectangle_le_plane_normalizer F D ha
  · intro a ha
    change (a : G) ∈ F.plane
    rw [← plane_centralizer_eq F]
    apply mem_centralizer_iff.mpr
    intro b hb
    have hh := mem_centralizer_iff.mp ha
      (⟨b, rectangle_le_edgeGroup F D hb⟩ : B) hb
    exact congrArg Subtype.val hh
  · intro n
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 N) n
  · change Odd ((threeSpaceNormalizer F).relIndex (edgeGroup F D))
    rw [edge_plane_index]
    decide
  · apply eq_bot_iff.mpr
    rintro a ⟨haN, haJ⟩
    have he : (⟨(a : G), haN⟩ : F.plane) = 1 := edge_plane_fixed_rectangle F D _ (by
      intro n hn
      have hh := mem_centralizer_iff.mp haJ n hn
      have hg := congrArg (fun b : B => (b : G)) hh
      change (n : G) * (a : G) = (a : G) * (n : G) at hg
      rw [hg, mul_inv_cancel_right])
    change a = 1
    exact Subtype.ext (congrArg (fun x : F.plane => (x : G)) he)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
